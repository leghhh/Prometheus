local Prometheus = require("src.prometheus")
Prometheus.Logger.logLevel = Prometheus.Logger.LogLevel.Error
Prometheus.Logger.logCallback = function() end
Prometheus.Logger.warnCallback = function() end

local Deobfuscator = Prometheus.Deobfuscator

local function cloneTable(t)
    if type(t) ~= "table" then
        return t
    end
    local out = {}
    for k, v in pairs(t) do
        out[k] = cloneTable(v)
    end
    return out
end

local function evalLua51(code)
    local outputs = {}
    local fn, loadErr = loadstring(code)
    if not fn then
        error("Syntax error in generated Lua 5.1 code: " .. tostring(loadErr) .. "\n" .. code)
    end
    local env = setmetatable({
        print = function(...)
            local n = select("#", ...)
            local parts = {}
            for i = 1, n do
                parts[i] = tostring(select(i, ...))
            end
            outputs[#outputs + 1] = table.concat(parts, "\t")
        end,
    }, { __index = _G })
    setfenv(fn, env)
    local rets = { fn() }
    return table.concat(outputs, "\n"), rets
end

local function verifyRoundTrip(name, source, config)
    local expectedOut = evalLua51(source)
    local cfg = cloneTable(config)
    cfg.LuaVersion = cfg.LuaVersion or "Lua51"
    cfg.Seed = cfg.Seed or 12345
    local obfuscated = Prometheus.Pipeline:fromConfig(cfg):apply(source)
    local deobf = Deobfuscator:new({ LuaVersion = cfg.LuaVersion })
    local recovered, report = deobf:deobfuscate(obfuscated)
    local actualOut = evalLua51(recovered)
    assert(actualOut == expectedOut, string.format(
        "[%s] output mismatch:\nexpected: %q\ngot:      %q\npasses:   %s\ncode:\n%s",
        name, expectedOut, actualOut, table.concat(report.appliedPasses, ","), recovered
    ))
    return recovered, report
end

local richProgram = [[
local base = 17
local function makeAdder(delta)
    local count = 0
    return function(x)
        count = count + 1
        local base = x * 2
        return base + delta + count
    end
end

local add3 = makeAdder(3)
local items = { "alpha\n\0beta", "caf\195\169", "", "\255\1\2" }
local sum = 0
for i = 1, 6 do
    if i % 2 == 1 and (i > 1 or base == 17) then
        sum = sum + add3(i)
    else
        sum = sum - (i % 3)
    end
end

local function variadic(head, ...)
    local n = select("#", ...)
    if n == 0 then
        return head, nil
    end
    return head + n, (...)
end

local a = variadic(10, "x", "y", "z")
local _, b = variadic(10, "x", "y", "z")
local c, d = (variadic(5, "only"))
print(sum, a, b, tostring(c), tostring(d), #items[1], items[2], #items[4])
]]

verifyRoundTrip("Step:NumbersToExpressions", richProgram, {
    Steps = { { Name = "NumbersToExpressions", Settings = { Threshold = 1, NumberRepresentationMutation = true } } },
})
verifyRoundTrip("Step:WrapInFunction", richProgram, {
    Steps = { { Name = "WrapInFunction", Settings = { Iterations = 2 } } },
})
verifyRoundTrip("Step:AddVararg", richProgram, {
    Steps = { { Name = "AddVararg", Settings = {} } },
})
verifyRoundTrip("Step:WatermarkCheck", richProgram, {
    Steps = { { Name = "WatermarkCheck", Settings = { Content = "WM_TEST_2026" } } },
})
verifyRoundTrip("Step:AntiTamperDefault", richProgram, {
    Steps = { { Name = "AntiTamper", Settings = { UseDebug = true } } },
})
verifyRoundTrip("Step:AntiTamperNoDebug", richProgram, {
    Steps = { { Name = "AntiTamper", Settings = { UseDebug = false } } },
})
for _, enc in ipairs({ "base64", "base85", "mixed" }) do
    verifyRoundTrip("Step:ConstantArray:" .. enc, richProgram, {
        Steps = {
            {
                Name = "ConstantArray",
                Settings = {
                    Treshold = 1,
                    StringsOnly = false,
                    Shuffle = true,
                    Rotate = true,
                    LocalWrapperTreshold = 1,
                    LocalWrapperCount = 3,
                    LocalWrapperArgCount = 4,
                    Encoding = enc,
                },
            },
        },
    })
end
for _, stype in ipairs({ "strcat", "table", "custom" }) do
    verifyRoundTrip("Step:SplitStrings:" .. stype, richProgram, {
        Steps = {
            {
                Name = "SplitStrings",
                Settings = {
                    Treshold = 1,
                    MinLength = 2,
                    MaxLength = 4,
                    ConcatenationType = stype,
                    CustomFunctionType = "local",
                    CustomLocalFunctionsCount = 2,
                },
            },
        },
    })
end
verifyRoundTrip("Step:EncryptStrings", richProgram, {
    Steps = { { Name = "EncryptStrings", Settings = {} } },
})
for _, ltype in ipairs({ "string", "number" }) do
    local proxSrc = [[
local total = 10
local label = "val:"
for i = 1, 5 do
    total = total + i * 2
end
local function scale(n)
    return total + n
end
print(label .. tostring(scale(7)))
]]
    verifyRoundTrip("Step:ProxifyLocals:" .. ltype, proxSrc, {
        Steps = { { Name = "ProxifyLocals", Settings = { LiteralType = ltype } } },
    })
end
verifyRoundTrip("Step:Cff", richProgram, {
    Steps = { { Name = "Cff", Settings = {} } },
})
verifyRoundTrip("Step:Vmify", richProgram, {
    Steps = { { Name = "Vmify", Settings = {} } },
})

for _, presetName in ipairs({ "Minify", "Weak", "Cff", "Vmify", "Medium", "Strong" }) do
    verifyRoundTrip("Preset:" .. presetName .. ":rich", richProgram, Prometheus.Presets[presetName])
end

for _, fixturePath in ipairs({
    "tests/ambiguous-call.lua",
    "tests/coroutines.lua",
    "tests/upvalues.lua",
    "tests/parenthesized-results.lua",
    "tests/gc-temporaries.lua",
}) do
    local f = assert(io.open(fixturePath, "rb"))
    local src = f:read("*a")
    f:close()
    for _, presetName in ipairs({ "Minify", "Weak", "Cff", "Vmify", "Medium", "Strong" }) do
        verifyRoundTrip("Fixture:" .. presetName .. ":" .. fixturePath, src, Prometheus.Presets[presetName])
    end
end

do
    local emptyRecovered = Deobfuscator:new({ LuaVersion = "Lua51" }):deobfuscate("")
    assert(evalLua51(emptyRecovered) == "")
    verifyRoundTrip("MinimalReturn", "local x = true and false or 42\nprint(x)\n", Prometheus.Presets.Strong)
end

do
    local obf = Prometheus.Pipeline:fromConfig(Prometheus.Presets.Strong):apply(richProgram)
    local r1 = Deobfuscator:new({ LuaVersion = "Lua51" }):deobfuscate(obf)
    local r2 = Deobfuscator:new({ LuaVersion = "Lua51" }):deobfuscate(obf)
    assert(r1 == r2, "Deobfuscation must be deterministic")
    local r3 = Deobfuscator:new({ LuaVersion = "Lua51" }):deobfuscate(r1)
    assert(evalLua51(r3) == evalLua51(richProgram), "Re-deobfuscation must preserve runtime behavior")
end

do
    local userCode = [[
local state = 1
local box = setmetatable({ value = 10 }, {
    __add = function(self, other)
        return self.value + other
    end,
    __index = function(_, key)
        return "missing:" .. tostring(key)
    end,
})
while state > 0 do
    if state == 1 then
        box.value = box + 5
        state = 2
    elseif state == 2 then
        print(box.value, box.extra)
        state = 0
    end
end
]]
    local outOrig = evalLua51(userCode)
    local untouched, rep = Deobfuscator:new({ LuaVersion = "Lua51" }):deobfuscate(userCode)
    assert(#rep.appliedPasses == 0, "Plain user code must not trigger false-positive structural passes")
    assert(untouched:find("box", 1, true) ~= nil and untouched:find("state", 1, true) ~= nil)
    assert(evalLua51(untouched) == outOrig)
end

do
    local luauCheck = io.popen("command -v luau 2>/dev/null", "r")
    local luauBin = luauCheck and luauCheck:read("*l") or nil
    if luauCheck then luauCheck:close() end

    local luauSrc = [[
local total = 0b1010_0000
for i = 1, 8 do
    if i % 2 == 0 then
        continue
    end
    total += i
end
local k = 0
local acc = ""
repeat
    k += 1
    if k == 2 then
        continue
    end
    acc ..= tostring(k)
until k >= 4 and #acc > 0
local function tag(n)
    return if n > 0 then "pos" elseif n < 0 then "neg" else "zero"
end
print(total, acc, tag(3), tag(-3), tag(0))
]]
    for _, presetName in ipairs({ "Minify", "Vmify", "Medium", "Strong" }) do
        local cfg = cloneTable(Prometheus.Presets[presetName])
        cfg.LuaVersion = "LuaU"
        local obf = Prometheus.Pipeline:fromConfig(cfg):apply(luauSrc)
        local rec = Deobfuscator:new({ LuaVersion = "LuaU" }):deobfuscate(obf)
        assert(type(rec) == "string" and #rec > 0)
        if luauBin and luauBin ~= "" then
            local tmpA = os.tmpname() .. ".luau"
            local tmpB = os.tmpname() .. ".luau"
            local fa = assert(io.open(tmpA, "wb")); fa:write(luauSrc); fa:close()
            local fb = assert(io.open(tmpB, "wb")); fb:write(rec); fb:close()
            local pa = io.popen("luau " .. tmpA .. " 2>&1", "r"); local oa = pa:read("*a"); pa:close()
            local pb = io.popen("luau " .. tmpB .. " 2>&1", "r"); local ob = pb:read("*a"); pb:close()
            os.remove(tmpA)
            os.remove(tmpB)
            assert(oa == ob, string.format("Luau preset %s mismatch: %q vs %q", presetName, oa, ob))
        end
    end
end

do
    local function runCli(cmdArgs)
        local p = io.popen("lua5.1 cli.lua " .. cmdArgs .. " 2>&1; printf '\\nEXIT:%d' $?", "r")
        local out = p:read("*a")
        p:close()
        local body, codeStr = out:match("^(.*)\nEXIT:(%d+)%s*$")
        return tonumber(codeStr), body or out
    end

    local codeHelp, outHelp = runCli("--help")
    assert(codeHelp == 0 and outHelp:find("Usage:", 1, true) ~= nil)

    local codeNoArgs = runCli("")
    assert(codeNoArgs ~= 0)

    local codeBadOpt = runCli("--nonexistent-flag")
    assert(codeBadOpt ~= 0)

    local codeMissingFile = runCli("/tmp/definitely_missing_prometheus_input_99999.lua")
    assert(codeMissingFile ~= 0)

    local badLua = os.tmpname() .. ".lua"
    local fb = assert(io.open(badLua, "wb")); fb:write("local x = then end ???"); fb:close()
    local codeMalformed, outMalformed = runCli(badLua)
    os.remove(badLua)
    assert(codeMalformed ~= 0 and outMalformed:find("Error:", 1, true) ~= nil)

    local baseTmp = os.tmpname()
    local inFile = baseTmp .. ".lua"
    local obfFile = baseTmp .. ".obfuscated.lua"
    local deobfFile = baseTmp .. ".deobfuscated.lua"
    local customOut = baseTmp .. ".custom.lua"
    local fi = assert(io.open(inFile, "wb")); fi:write("local a = 21\nprint(a * 2)\n"); fi:close()

    local codeObf = runCli("--preset Medium " .. inFile)
    assert(codeObf == 0)

    local codeDeobf, outDeobf = runCli(obfFile)
    assert(codeDeobf == 0 and outDeobf == "", "Standard CLI deobfuscation must emit zero banner noise")

    local fd = assert(io.open(deobfFile, "rb")); local deobfSrc = fd:read("*a"); fd:close()
    assert(evalLua51(deobfSrc) == "42")

    local fo = assert(io.open(obfFile, "rb")); local obfStillIntact = fo:read("*a"); fo:close()
    assert(obfStillIntact ~= deobfSrc, "Input file must not be overwritten by default")

    local codePasses, outPasses = runCli("--passes -o " .. customOut .. " " .. obfFile)
    assert(codePasses == 0 and outPasses:find("Passes:", 1, true) ~= nil)
    local fc = assert(io.open(customOut, "rb")); local customSrc = fc:read("*a"); fc:close()
    assert(customSrc == deobfSrc)

    os.remove(baseTmp)
    os.remove(inFile)
    os.remove(obfFile)
    os.remove(deobfFile)
    os.remove(customOut)
end

print("All deobfuscator regression and CLI checks passed")

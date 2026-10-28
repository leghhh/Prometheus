local function script_path()
    local str = debug.getinfo(2, "S").source:sub(2)
    return str:match("(.*[/%\\])") or ""
end
package.path = script_path() .. "?.lua;" .. package.path

local function get_version()
    local version = os.getenv("PROMETHEUS_LUA_VERSION")
    if version and version ~= "" then
        return version
    end
    return "v0.3"
end

local function print_help()
    print("Usage: prometheus-lua [command] [options] <input.lua>")
    print("")
    print("Commands:")
    print("  deobfuscate            Deobfuscate a Prometheus-obfuscated file (default)")
    print("  obfuscate              Obfuscate a Lua / Luau source file")
    print("")
    print("Options:")
    print("  -o, --out <file>       Output file path")
    print("  --stdout               Write output to standard output")
    print("  --Lua51, --lua51       Force Lua 5.1 dialect")
    print("  --LuaU, --luau         Force Luau dialect")
    print("  --passes               Print applied deobfuscation passes to stderr")
    print("  --no-rename            Skip identifier normalization")
    print("  --preset, --p <name>   Obfuscate using preset (Minify, Weak, Cff, Vmify, Medium, Strong)")
    print("  --config, --c <file>   Obfuscate using custom config file")
    print("  --pretty               Pretty-print obfuscated output")
    print("  --nocolors             Disable ANSI colors in diagnostics")
    print("  -v, --version          Print version")
    print("  -h, --help             Print this help message")
end

local function fail(msg)
    io.stderr:write("Error: " .. tostring(msg) .. "\n")
    os.exit(1)
end

local function read_all_bytes(path)
    local handle, openErr = io.open(path, "rb")
    if not handle then
        return nil, openErr or ("Cannot open file: " .. tostring(path))
    end
    local content, readErr = handle:read("*a")
    handle:close()
    if content == nil then
        return nil, readErr or ("Cannot read file: " .. tostring(path))
    end
    return content
end

local function write_all_bytes(path, content)
    local handle, openErr = io.open(path, "wb")
    if not handle then
        return false, openErr or ("Cannot open output file: " .. tostring(path))
    end
    local ok, writeErr = handle:write(content)
    handle:close()
    if not ok then
        return false, writeErr or ("Cannot write output file: " .. tostring(path))
    end
    return true
end

local function load_chunk(content, chunkName, environment)
    if type(loadstring) == "function" then
        local func, err = loadstring(content, chunkName)
        if not func then
            return nil, err
        end
        if environment and type(setfenv) == "function" then
            setfenv(func, environment)
        elseif environment and type(load) == "function" then
            return load(content, chunkName, "t", environment)
        end
        return func
    end
    if type(load) ~= "function" then
        return nil, "No load function available"
    end
    return load(content, chunkName, "t", environment)
end

local function derive_deobfuscated_path(sourceFile)
    local out
    if sourceFile:sub(-15) == ".obfuscated.lua" then
        out = sourceFile:sub(1, -16) .. ".deobfuscated.lua"
    elseif sourceFile:sub(-16) == ".obfuscated.luau" then
        out = sourceFile:sub(1, -17) .. ".deobfuscated.luau"
    elseif sourceFile:sub(-5) == ".luau" then
        out = sourceFile:sub(1, -6) .. ".deobfuscated.luau"
    elseif sourceFile:sub(-4) == ".lua" then
        out = sourceFile:sub(1, -5) .. ".deobfuscated.lua"
    else
        out = sourceFile .. ".deobfuscated.lua"
    end
    if out == sourceFile then
        out = sourceFile .. ".out.lua"
    end
    return out
end

local function derive_obfuscated_path(sourceFile)
    local out
    if sourceFile:sub(-5) == ".luau" then
        out = sourceFile:sub(1, -6) .. ".obfuscated.luau"
    elseif sourceFile:sub(-4) == ".lua" then
        out = sourceFile:sub(1, -5) .. ".obfuscated.lua"
    else
        out = sourceFile .. ".obfuscated.lua"
    end
    if out == sourceFile then
        out = sourceFile .. ".out.lua"
    end
    return out
end

local args = type(arg) == "table" and arg or {}

if #args == 0 then
    fail("No input file specified. Run with --help for usage.")
end

if args[1] == "--help" or args[1] == "-h" or args[1] == "help" then
    print_help()
    os.exit(0)
end

if args[1] == "--version" or args[1] == "-v" then
    print(get_version())
    os.exit(0)
end

local Prometheus = require("prometheus")

local mode = nil
local sourceFile = nil
local outFile = nil
local writeStdout = false
local luaVersion = nil
local inspectPasses = false
local normalizeIds = true
local presetName = nil
local configFile = nil
local prettyPrint = nil
local noColors = false

local i = 1
if args[1] == "deobfuscate" then
    mode = "deobfuscate"
    i = 2
elseif args[1] == "obfuscate" then
    mode = "obfuscate"
    i = 2
end

while i <= #args do
    local curr = args[i]
    if curr == "--help" or curr == "-h" then
        print_help()
        os.exit(0)
    elseif curr == "--version" or curr == "-v" then
        print(get_version())
        os.exit(0)
    elseif curr == "-d" or curr == "--deobfuscate" then
        if mode == "obfuscate" then
            fail("Cannot combine obfuscate and deobfuscate modes")
        end
        mode = "deobfuscate"
    elseif curr == "-o" or curr == "--o" or curr == "--out" then
        i = i + 1
        if i > #args or args[i] == "" then
            fail("Option " .. curr .. " requires an output file path")
        end
        outFile = args[i]
    elseif curr == "--stdout" then
        writeStdout = true
    elseif curr == "--Lua51" or curr == "--lua51" then
        luaVersion = "Lua51"
    elseif curr == "--LuaU" or curr == "--luau" then
        luaVersion = "LuaU"
    elseif curr == "--passes" or curr == "--report" then
        inspectPasses = true
    elseif curr == "--no-rename" then
        normalizeIds = false
    elseif curr == "--nocolors" then
        noColors = true
    elseif curr == "--pretty" then
        prettyPrint = true
    elseif curr == "--preset" or curr == "--p" then
        if mode == "deobfuscate" then
            fail("Cannot use --preset in deobfuscate mode")
        end
        mode = "obfuscate"
        i = i + 1
        if i > #args or args[i] == "" then
            fail("Option " .. curr .. " requires a preset name")
        end
        presetName = args[i]
    elseif curr == "--config" or curr == "--c" then
        if mode == "deobfuscate" then
            fail("Cannot use --config in deobfuscate mode")
        end
        mode = "obfuscate"
        i = i + 1
        if i > #args or args[i] == "" then
            fail("Option " .. curr .. " requires a config file path")
        end
        configFile = args[i]
    elseif curr:sub(1, 1) == "-" then
        fail("Unknown option: " .. tostring(curr))
    else
        if sourceFile ~= nil then
            fail("Unexpected argument: " .. tostring(curr))
        end
        sourceFile = curr
    end
    i = i + 1
end

if not sourceFile or sourceFile == "" then
    fail("No input file specified")
end

if not mode then
    mode = "deobfuscate"
end

Prometheus.colors.enabled = not noColors

local source, readErr = read_all_bytes(sourceFile)
if source == nil then
    fail(readErr)
end

if mode == "obfuscate" then
    Prometheus.Logger.logLevel = Prometheus.Logger.LogLevel.Error
    Prometheus.Logger.errorCallback = function(...)
        local msgParts = { ... }
        fail(table.concat(msgParts, " "))
    end

    local config
    if configFile then
        local cfgContent, cfgReadErr = read_all_bytes(configFile)
        if cfgContent == nil then
            fail(cfgReadErr)
        end
        local func, loadErr = load_chunk(cfgContent, "@" .. configFile, {})
        if not func then
            fail("Failed to parse config file \"" .. configFile .. "\": " .. tostring(loadErr))
        end
        local okCfg, cfgRes = pcall(func)
        if not okCfg or type(cfgRes) ~= "table" then
            fail("Invalid config file \"" .. configFile .. "\"")
        end
        config = cfgRes
    elseif presetName then
        local preset = Prometheus.Presets[presetName]
        if not preset then
            fail("Unknown preset: " .. tostring(presetName))
        end
        config = {}
        for k, v in pairs(preset) do
            config[k] = v
        end
    else
        config = {}
        for k, v in pairs(Prometheus.Presets.Minify) do
            config[k] = v
        end
    end

    if luaVersion then
        config.LuaVersion = luaVersion
    end
    if prettyPrint ~= nil then
        config.PrettyPrint = prettyPrint
    end

    local okObf, obfOut = pcall(function()
        local pipeline = Prometheus.Pipeline:fromConfig(config)
        return pipeline:apply(source, sourceFile)
    end)
    if not okObf then
        local cleaned = tostring(obfOut):gsub("^.-:%d+:%s*", "")
        fail(cleaned)
    end

    if writeStdout then
        io.stdout:write(obfOut)
    else
        local targetOut = outFile or derive_obfuscated_path(sourceFile)
        local okW, wErr = write_all_bytes(targetOut, obfOut)
        if not okW then
            fail(wErr)
        end
    end
    os.exit(0)
end

Prometheus.Logger.logLevel = Prometheus.Logger.LogLevel.Error
Prometheus.Logger.logCallback = function() end
Prometheus.Logger.warnCallback = function() end

local deobf = Prometheus.Deobfuscator:new({
    LuaVersion = luaVersion or "Auto",
    TargetLuaVersion = luaVersion,
    NormalizeIdentifiers = normalizeIds,
})

local okDeobf, result, report = pcall(function()
    return deobf:deobfuscate(source)
end)

if not okDeobf then
    local cleaned = tostring(result):gsub("^.-:%d+:%s*", "")
    fail(cleaned)
end

if inspectPasses and report then
    local passSummary = #report.appliedPasses > 0 and table.concat(report.appliedPasses, " -> ") or "(none)"
    io.stderr:write(string.format(
        "Dialect: %s | Iterations: %d | Passes: %s\n",
        tostring(report.luaVersion),
        tonumber(report.iterations) or 0,
        passSummary
    ))
end

if writeStdout then
    io.stdout:write(result)
else
    local targetOut = outFile or derive_deobfuscated_path(sourceFile)
    local okW, wErr = write_all_bytes(targetOut, result)
    if not okW then
        fail(wErr)
    end
end

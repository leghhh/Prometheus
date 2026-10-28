local function script_dir()
    local info = debug and debug.getinfo and debug.getinfo(1, "S")
    local src = info and info.source or ""
    if src:sub(1, 1) == "@" then
        src = src:sub(2)
    end
    return src:match("^(.*[/%\\])") or "./"
end

local rootDir = script_dir()
package.path = rootDir .. "src/?.lua;" .. package.path

local VERSION = "1.0.0"

local function print_help()
    print("Usage: lua cli.lua [options] <input.lua>")
    print("")
    print("Options:")
    print("  -o, --out <file>       Output file path")
    print("  --stdout               Write deobfuscated output to stdout")
    print("  --Lua51, --lua51       Force Lua 5.1 dialect")
    print("  --LuaU, --luau         Force Luau dialect")
    print("  --detect               Inspect detected Prometheus layers and exit")
    print("  --passes               Print detected layers and applied passes to stderr")
    print("  --no-rename            Skip identifier normalization")
    print("  -f, --force            Allow overwriting input file when -o matches input")
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

local function derive_output_path(sourceFile)
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

local args = type(arg) == "table" and arg or {}
if #args == 0 then
    fail("No input file specified. Run with --help for usage.")
end

local sourceFile = nil
local outFile = nil
local writeStdout = false
local luaVersion = nil
local detectOnly = false
local showPasses = false
local normalizeIds = true
local forceOverwrite = false

local i = 1
if args[1] == "deobfuscate" then
    i = 2
end

while i <= #args do
    local curr = args[i]
    if curr == "-h" or curr == "--help" or curr == "help" then
        print_help()
        os.exit(0)
    elseif curr == "-v" or curr == "--version" then
        print(VERSION)
        os.exit(0)
    elseif curr == "-d" or curr == "--deobfuscate" then
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
    elseif curr == "--detect" then
        detectOnly = true
    elseif curr == "--passes" or curr == "--report" then
        showPasses = true
    elseif curr == "--no-rename" then
        normalizeIds = false
    elseif curr == "-f" or curr == "--force" then
        forceOverwrite = true
    elseif curr:sub(1, 1) == "-" then
        fail("Unknown option: " .. curr)
    else
        if sourceFile then
            fail("Unexpected positional argument: " .. curr)
        end
        sourceFile = curr
    end
    i = i + 1
end

if not sourceFile then
    fail("No input file specified.")
end

local source, readErr = read_all_bytes(sourceFile)
if source == nil then
    fail(readErr)
end

local Prometheus = require("prometheus")
Prometheus.Logger.logCallback = function() end
Prometheus.Logger.warnCallback = function() end
Prometheus.Logger.debugCallback = function() end
Prometheus.Logger.errorCallback = function(msg)
    error(tostring(msg), 0)
end

local deobfuscator = Prometheus.Deobfuscator:new({
    LuaVersion = luaVersion,
    NormalizeIdentifiers = normalizeIds,
})

if detectOnly then
    local okDet, detOrErr = pcall(function()
        return deobfuscator:detect(source)
    end)
    if not okDet then
        fail(detOrErr)
    end
    local layers = #detOrErr.layers > 0 and table.concat(detOrErr.layers, ", ") or "none"
    print(string.format("Prometheus: %s", tostring(detOrErr.isPrometheus)))
    print(string.format("Dialect: %s", tostring(detOrErr.luaVersion)))
    print(string.format("Detected: %s", layers))
    print(string.format("FirstPass: %s", tostring(detOrErr.recommendedFirstPass or "none")))
    os.exit(0)
end

local ok, outputOrErr, report = pcall(function()
    return deobfuscator:deobfuscate(source)
end)
if not ok then
    fail(outputOrErr)
end

if showPasses and report and report.appliedPasses then
    local detLayers = (report.detected and report.detected.layers and #report.detected.layers > 0)
        and table.concat(report.detected.layers, ", ") or "none"
    local list = #report.appliedPasses > 0 and table.concat(report.appliedPasses, " -> ") or "none"
    io.stderr:write(string.format("Dialect: %s | Initial: %s | Passes: %s\n", tostring(report.luaVersion), detLayers, list))
end

if writeStdout then
    io.stdout:write(outputOrErr)
    if outputOrErr:sub(-1) ~= "\n" then
        io.stdout:write("\n")
    end
end

if outFile or not writeStdout then
    local target = outFile or derive_output_path(sourceFile)
    if target == sourceFile and not forceOverwrite then
        fail("Refusing to overwrite input file without --force: " .. tostring(sourceFile))
    end
    local wroteOk, writeErr = write_all_bytes(target, outputOrErr)
    if not wroteOk then
        fail(writeErr)
    end
end

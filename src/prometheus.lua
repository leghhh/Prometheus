local function script_path()
    local str = debug.getinfo(2, "S").source:sub(2)
    return str:match("(.*[/%\\])") or ""
end

local oldPkgPath = package.path
package.path = script_path() .. "?.lua;" .. package.path

if not pcall(function()
    return math.random(1, 2 ^ 40)
end) then
    local oldMathRandom = math.random
    math.random = function(a, b)
        if not a and not b then
            return oldMathRandom()
        end
        if not a and b then
            return oldMathRandom()
        end
        if not b then
            return math.random(1, a)
        end
        if a > b then
            a, b = b, a
        end
        local diff = b - a
        assert(diff >= 0)
        if diff > 2 ^ 31 - 1 then
            return math.floor(oldMathRandom() * diff + a)
        else
            return oldMathRandom(a, b)
        end
    end
end

_G.newproxy = _G.newproxy or function(useMt)
    if useMt then
        return setmetatable({}, {})
    end
    return {}
end

local Pipeline = require("prometheus.pipeline")
local Deobfuscator = require("prometheus.deobfuscator")
local Formatter = require("prometheus.formatter")
local highlight = require("highlightlua")
local colors = require("colors")
local Logger = require("logger")
local Presets = require("presets")
local Config = require("config")
local util = require("prometheus.util")

package.path = oldPkgPath

return {
    Pipeline = Pipeline,
    Deobfuscator = Deobfuscator,
    Formatter = Formatter,
    colors = colors,
    Config = util.readonly(Config),
    Logger = Logger,
    highlight = highlight,
    Presets = Presets,
}

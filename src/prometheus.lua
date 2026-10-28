local function script_path()
    local str = debug.getinfo(2, "S").source:sub(2)
    return str:match("(.*[/%\\])") or ""
end

local oldPkgPath = package.path
package.path = script_path() .. "?.lua;" .. package.path

local Deobfuscator = require("prometheus.deobfuscator")
local Formatter = require("prometheus.formatter")
local Parser = require("prometheus.parser")
local Tokenizer = require("prometheus.tokenizer")
local Ast = require("prometheus.ast")
local Scope = require("prometheus.scope")
local Enums = require("prometheus.enums")
local Logger = require("logger")

package.path = oldPkgPath

return {
    Deobfuscator = Deobfuscator,
    Formatter = Formatter,
    Parser = Parser,
    Tokenizer = Tokenizer,
    Ast = Ast,
    Scope = Scope,
    Enums = Enums,
    Logger = Logger,
}

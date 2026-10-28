local Ast = require("prometheus.ast")
local Enums = require("prometheus.enums")
local util = require("prometheus.util")

local AstKind = Ast.AstKind
local LuaVersion = Enums.LuaVersion
local lookupify = util.lookupify

local Formatter = {}
Formatter.__index = Formatter

local LUA51_KEYWORDS = lookupify({
    "and", "break", "do", "else", "elseif", "end", "false", "for",
    "function", "if", "in", "local", "nil", "not", "or", "repeat",
    "return", "then", "true", "until", "while",
})

local LUAU_KEYWORDS = lookupify({
    "and", "break", "do", "else", "elseif", "end", "false", "for",
    "function", "if", "in", "local", "nil", "not", "or", "repeat",
    "return", "then", "true", "until", "while", "continue",
})

local BINARY_OPS = {
    [AstKind.OrExpression] = { op = "or", prec = 1, assoc = "left" },
    [AstKind.AndExpression] = { op = "and", prec = 2, assoc = "left" },
    [AstKind.LessThanExpression] = { op = "<", prec = 3, assoc = "none" },
    [AstKind.GreaterThanExpression] = { op = ">", prec = 3, assoc = "none" },
    [AstKind.LessThanOrEqualsExpression] = { op = "<=", prec = 3, assoc = "none" },
    [AstKind.GreaterThanOrEqualsExpression] = { op = ">=", prec = 3, assoc = "none" },
    [AstKind.NotEqualsExpression] = { op = "~=", prec = 3, assoc = "none" },
    [AstKind.EqualsExpression] = { op = "==", prec = 3, assoc = "none" },
    [AstKind.StrCatExpression] = { op = "..", prec = 4, assoc = "right" },
    [AstKind.AddExpression] = { op = "+", prec = 5, assoc = "left" },
    [AstKind.SubExpression] = { op = "-", prec = 5, assoc = "left" },
    [AstKind.MulExpression] = { op = "*", prec = 6, assoc = "left" },
    [AstKind.DivExpression] = { op = "/", prec = 6, assoc = "left" },
    [AstKind.ModExpression] = { op = "%", prec = 6, assoc = "left" },
    [AstKind.PowExpression] = { op = "^", prec = 8, assoc = "right" },
}

local UNARY_OPS = {
    [AstKind.NotExpression] = "not ",
    [AstKind.NegateExpression] = "-",
    [AstKind.LenExpression] = "#",
}

local COMPOUND_OPS = {
    [AstKind.CompoundAddStatement] = { op = "+=", bin = Ast.AddExpression },
    [AstKind.CompoundSubStatement] = { op = "-=", bin = Ast.SubExpression },
    [AstKind.CompoundMulStatement] = { op = "*=", bin = Ast.MulExpression },
    [AstKind.CompoundDivStatement] = { op = "/=", bin = Ast.DivExpression },
    [AstKind.CompoundModStatement] = { op = "%=", bin = Ast.ModExpression },
    [AstKind.CompoundPowStatement] = { op = "^=", bin = Ast.PowExpression },
    [AstKind.CompoundConcatStatement] = { op = "..=", bin = Ast.StrCatExpression },
}

local PRIMARY_BASES = lookupify({
    AstKind.VariableExpression,
    AstKind.IndexExpression,
    AstKind.FunctionCallExpression,
    AstKind.PassSelfFunctionCallExpression,
})

function Formatter:new(settings)
    settings = settings or {}
    local luaVersion = settings.LuaVersion or settings.luaVersion or LuaVersion.Lua51
    local instance = {
        luaVersion = luaVersion,
        indent = settings.indent or "    ",
        keywords = luaVersion == LuaVersion.LuaU and LUAU_KEYWORDS or LUA51_KEYWORDS,
    }
    return setmetatable(instance, Formatter)
end

function Formatter:isValidIdentifier(name)
    if type(name) ~= "string" or #name == 0 then
        return false
    end
    if self.keywords[name] then
        return false
    end
    return string.match(name, "^[A-Za-z_][A-Za-z0-9_]*$") ~= nil
end

local function utf8SeqLength(str, pos, len)
    local b1 = string.byte(str, pos)
    if b1 >= 0xC2 and b1 <= 0xDF then
        if pos + 1 > len then return 0 end
        local b2 = string.byte(str, pos + 1)
        if b2 >= 0x80 and b2 <= 0xBF then return 2 end
        return 0
    elseif b1 >= 0xE0 and b1 <= 0xEF then
        if pos + 2 > len then return 0 end
        local b2, b3 = string.byte(str, pos + 1, pos + 2)
        if b1 == 0xE0 and (b2 < 0xA0 or b2 > 0xBF) then return 0 end
        if b1 == 0xED and (b2 < 0x80 or b2 > 0x9F) then return 0 end
        if b2 >= 0x80 and b2 <= 0xBF and b3 >= 0x80 and b3 <= 0xBF then return 3 end
        return 0
    elseif b1 >= 0xF0 and b1 <= 0xF4 then
        if pos + 3 > len then return 0 end
        local b2, b3, b4 = string.byte(str, pos + 1, pos + 3)
        if b1 == 0xF0 and (b2 < 0x90 or b2 > 0xBF) then return 0 end
        if b1 == 0xF4 and (b2 < 0x80 or b2 > 0x8F) then return 0 end
        if b2 >= 0x80 and b2 <= 0xBF and b3 >= 0x80 and b3 <= 0xBF and b4 >= 0x80 and b4 <= 0xBF then
            return 4
        end
        return 0
    end
    return 0
end

function Formatter:formatString(val)
    local out = { '"' }
    local len = #val
    local i = 1
    while i <= len do
        local b = string.byte(val, i)
        if b == 34 then
            out[#out + 1] = '\\"'
            i = i + 1
        elseif b == 92 then
            out[#out + 1] = "\\\\"
            i = i + 1
        elseif b == 7 then
            out[#out + 1] = "\\a"
            i = i + 1
        elseif b == 8 then
            out[#out + 1] = "\\b"
            i = i + 1
        elseif b == 9 then
            out[#out + 1] = "\\t"
            i = i + 1
        elseif b == 10 then
            out[#out + 1] = "\\n"
            i = i + 1
        elseif b == 11 then
            out[#out + 1] = "\\v"
            i = i + 1
        elseif b == 12 then
            out[#out + 1] = "\\f"
            i = i + 1
        elseif b == 13 then
            out[#out + 1] = "\\r"
            i = i + 1
        elseif b >= 32 and b <= 126 then
            out[#out + 1] = string.sub(val, i, i)
            i = i + 1
        else
            local seqLen = utf8SeqLength(val, i, len)
            if seqLen > 0 then
                out[#out + 1] = string.sub(val, i, i + seqLen - 1)
                i = i + seqLen
            else
                local nextByte = i < len and string.byte(val, i + 1) or nil
                if nextByte and nextByte >= 48 and nextByte <= 57 then
                    out[#out + 1] = string.format("\\%03d", b)
                else
                    out[#out + 1] = string.format("\\%d", b)
                end
                i = i + 1
            end
        end
    end
    out[#out + 1] = '"'
    return table.concat(out)
end

function Formatter:formatNumber(value)
    if type(value) ~= "number" then
        return tostring(value)
    end
    if value ~= value then
        return "(0 / 0)", 0
    end
    if value == math.huge then
        return "2e1024", 10
    end
    if value == -math.huge then
        return "-2e1024", 7
    end
    if value == 0 and 1 / value < 0 then
        return "-0", 7
    end
    local str = tostring(value)
    if tonumber(str) ~= value then
        str = string.format("%.17g", value)
    end
    if string.sub(str, 1, 1) == "-" then
        return str, 7
    end
    return str, 10
end

function Formatter:pad(depth)
    if depth <= 0 then
        return ""
    end
    return string.rep(self.indent, depth)
end

function Formatter:formatArgs(args, depth)
    local out = {}
    for i = 1, #args do
        out[i] = self:formatExpression(args[i], depth)
    end
    return table.concat(out, ", ")
end

function Formatter:formatParams(args)
    local out = {}
    for i = 1, #args do
        local arg = args[i]
        if arg.kind == AstKind.VarargExpression then
            out[i] = "..."
        else
            out[i] = arg.scope:getVariableName(arg.id)
        end
    end
    return table.concat(out, ", ")
end

function Formatter:formatBase(expr, depth)
    local text = self:formatExpression(expr, depth)
    if not PRIMARY_BASES[expr.kind] or expr.isParenthesizedExpression then
        if not expr.isParenthesizedExpression then
            return "(" .. text .. ")"
        end
    end
    return text
end

function Formatter:exprPrecedence(expr)
    if expr.isParenthesizedExpression then
        return 10
    end
    local bin = BINARY_OPS[expr.kind]
    if bin then
        return bin.prec
    end
    if UNARY_OPS[expr.kind] then
        return 7
    end
    if expr.kind == AstKind.NumberExpression then
        local _, prec = self:formatNumber(expr.value)
        return prec
    end
    if expr.kind == AstKind.IfElseExpression then
        return 0
    end
    if expr.kind == AstKind.FunctionLiteralExpression then
        return 0
    end
    return 10
end

function Formatter:formatExpression(expr, depth)
    depth = depth or 0
    local raw = self:formatExpressionRaw(expr, depth)
    if expr.isParenthesizedExpression then
        if string.sub(raw, 1, 1) == "(" and string.sub(raw, -1) == ")" and expr.kind == AstKind.NumberExpression then
            return raw
        end
        return "(" .. raw .. ")"
    end
    return raw
end

function Formatter:formatExpressionRaw(expr, depth)
    local kind = expr.kind

    if kind == AstKind.BooleanExpression then
        return expr.value and "true" or "false"
    end
    if kind == AstKind.NilExpression then
        return "nil"
    end
    if kind == AstKind.VarargExpression then
        return "..."
    end
    if kind == AstKind.NumberExpression then
        local s = self:formatNumber(expr.value)
        return s
    end
    if kind == AstKind.StringExpression then
        return self:formatString(expr.value)
    end
    if kind == AstKind.VariableExpression then
        return expr.scope:getVariableName(expr.id)
    end

    if kind == AstKind.IndexExpression then
        local base = self:formatBase(expr.base, depth)
        if expr.index.kind == AstKind.StringExpression and self:isValidIdentifier(expr.index.value) then
            return base .. "." .. expr.index.value
        end
        return base .. "[" .. self:formatExpression(expr.index, depth) .. "]"
    end

    if kind == AstKind.FunctionCallExpression then
        local base = self:formatBase(expr.base, depth)
        return base .. "(" .. self:formatArgs(expr.args, depth) .. ")"
    end

    if kind == AstKind.PassSelfFunctionCallExpression then
        local base = self:formatBase(expr.base, depth)
        return base .. ":" .. expr.passSelfFunctionName .. "(" .. self:formatArgs(expr.args, depth) .. ")"
    end

    if kind == AstKind.FunctionLiteralExpression then
        local params = self:formatParams(expr.args)
        local stmts = expr.body.statements
        if #stmts == 0 then
            return "function(" .. params .. ") end"
        end
        local bodyText = self:formatBlock(expr.body, depth + 1)
        return "function(" .. params .. ")\n" .. bodyText .. "\n" .. self:pad(depth) .. "end"
    end

    if kind == AstKind.TableConstructorExpression then
        local entries = expr.entries
        if #entries == 0 then
            return "{}"
        end
        local parts = {}
        local multiline = #entries > 6
        for i = 1, #entries do
            local entry = entries[i]
            local item
            if entry.kind == AstKind.TableEntry then
                item = self:formatExpression(entry.value, multiline and (depth + 1) or depth)
            else
                if entry.key.kind == AstKind.StringExpression and self:isValidIdentifier(entry.key.value) then
                    item = entry.key.value .. " = " .. self:formatExpression(entry.value, multiline and (depth + 1) or depth)
                else
                    item = "[" .. self:formatExpression(entry.key, multiline and (depth + 1) or depth) .. "] = " .. self:formatExpression(entry.value, multiline and (depth + 1) or depth)
                end
            end
            if string.find(item, "\n", 1, true) then
                multiline = true
            end
            parts[i] = item
        end
        if not multiline then
            local joined = "{ " .. table.concat(parts, ", ") .. " }"
            if #joined <= 88 then
                return joined
            end
        end
        local lines = { "{" }
        local innerPad = self:pad(depth + 1)
        for i = 1, #entries do
            local entry = entries[i]
            local item
            if entry.kind == AstKind.TableEntry then
                item = self:formatExpression(entry.value, depth + 1)
            elseif entry.key.kind == AstKind.StringExpression and self:isValidIdentifier(entry.key.value) then
                item = entry.key.value .. " = " .. self:formatExpression(entry.value, depth + 1)
            else
                item = "[" .. self:formatExpression(entry.key, depth + 1) .. "] = " .. self:formatExpression(entry.value, depth + 1)
            end
            lines[#lines + 1] = innerPad .. item .. ","
        end
        lines[#lines + 1] = self:pad(depth) .. "}"
        return table.concat(lines, "\n")
    end

    if kind == AstKind.IfElseExpression then
        if self.luaVersion == LuaVersion.LuaU then
            local parts = {
                "if ",
                self:formatExpression(expr.condition, depth),
                " then ",
                self:formatExpression(expr.true_value, depth),
            }
            if expr.elseifs then
                for i = 1, #expr.elseifs do
                    local eif = expr.elseifs[i]
                    parts[#parts + 1] = " elseif "
                    parts[#parts + 1] = self:formatExpression(eif.condition, depth)
                    parts[#parts + 1] = " then "
                    parts[#parts + 1] = self:formatExpression(eif.value, depth)
                end
            end
            parts[#parts + 1] = " else "
            parts[#parts + 1] = self:formatExpression(expr.false_value, depth)
            return table.concat(parts)
        end
        local cond = self:formatExpression(expr.condition, depth + 1)
        local tv = self:formatExpression(expr.true_value, depth + 2)
        local fv = self:formatExpression(expr.false_value, depth + 2)
        local p1 = self:pad(depth + 1)
        local p2 = self:pad(depth + 2)
        local eifStr = ""
        if expr.elseifs then
            for i = 1, #expr.elseifs do
                local eif = expr.elseifs[i]
                eifStr = eifStr .. p1 .. "elseif " .. self:formatExpression(eif.condition, depth + 1) .. " then\n"
                    .. p2 .. "return " .. self:formatExpression(eif.value, depth + 2) .. "\n"
            end
        end
        return "(function()\n"
            .. p1 .. "if " .. cond .. " then\n"
            .. p2 .. "return " .. tv .. "\n"
            .. eifStr
            .. p1 .. "else\n"
            .. p2 .. "return " .. fv .. "\n"
            .. p1 .. "end\n"
            .. self:pad(depth) .. "end)()"
    end

    local unary = UNARY_OPS[kind]
    if unary then
        local sub = expr.rhs
        local subText = self:formatExpression(sub, depth)
        local subPrec = self:exprPrecedence(sub)
        if subPrec < 7 and not sub.isParenthesizedExpression then
            subText = "(" .. subText .. ")"
        elseif kind == AstKind.NegateExpression and string.sub(subText, 1, 1) == "-" then
            subText = "(" .. subText .. ")"
        end
        return unary .. subText
    end

    local bin = BINARY_OPS[kind]
    if bin then
        local lhs = expr.lhs
        local rhs = expr.rhs
        local lhsText = self:formatExpression(lhs, depth)
        local rhsText = self:formatExpression(rhs, depth)
        local lhsPrec = self:exprPrecedence(lhs)
        local rhsPrec = self:exprPrecedence(rhs)

        local wrapLhs = false
        local wrapRhs = false

        if bin.assoc == "left" then
            wrapLhs = lhsPrec < bin.prec
            wrapRhs = rhsPrec <= bin.prec
        elseif bin.assoc == "right" then
            if kind == AstKind.PowExpression then
                wrapLhs = lhsPrec <= 8
                wrapRhs = rhsPrec < 7
            else
                wrapLhs = lhsPrec <= bin.prec
                wrapRhs = rhsPrec < bin.prec
            end
        else
            wrapLhs = lhsPrec <= bin.prec
            wrapRhs = rhsPrec <= bin.prec
        end

        if wrapLhs and not lhs.isParenthesizedExpression then
            lhsText = "(" .. lhsText .. ")"
        end
        if wrapRhs and not rhs.isParenthesizedExpression then
            rhsText = "(" .. rhsText .. ")"
        end

        return lhsText .. " " .. bin.op .. " " .. rhsText
    end

    error("Unsupported expression kind: " .. tostring(kind))
end

function Formatter:formatLhs(lhs, depth)
    if lhs.kind == AstKind.AssignmentVariable then
        return lhs.scope:getVariableName(lhs.id)
    end
    if lhs.kind == AstKind.AssignmentIndexing then
        local base = self:formatBase(lhs.base, depth)
        if lhs.index.kind == AstKind.StringExpression and self:isValidIdentifier(lhs.index.value) then
            return base .. "." .. lhs.index.value
        end
        return base .. "[" .. self:formatExpression(lhs.index, depth) .. "]"
    end
    error("Unsupported assignment target kind: " .. tostring(lhs.kind))
end

function Formatter:formatStatement(stmt, depth)
    local kind = stmt.kind
    local pad = self:pad(depth)

    if kind == AstKind.BreakStatement then
        return pad .. "break"
    end

    if kind == AstKind.ContinueStatement then
        if self.luaVersion == LuaVersion.LuaU then
            return pad .. "continue"
        end
        error("ContinueStatement cannot be formatted directly in Lua51")
    end

    if kind == AstKind.DoStatement then
        if #stmt.body.statements == 0 then
            return pad .. "do end"
        end
        return pad .. "do\n" .. self:formatBlock(stmt.body, depth + 1) .. "\n" .. pad .. "end"
    end

    if kind == AstKind.WhileStatement then
        local cond = self:formatExpression(stmt.condition, depth)
        if #stmt.body.statements == 0 then
            return pad .. "while " .. cond .. " do end"
        end
        return pad .. "while " .. cond .. " do\n" .. self:formatBlock(stmt.body, depth + 1) .. "\n" .. pad .. "end"
    end

    if kind == AstKind.RepeatStatement then
        local cond = self:formatExpression(stmt.condition, depth)
        if #stmt.body.statements == 0 then
            return pad .. "repeat until " .. cond
        end
        return pad .. "repeat\n" .. self:formatBlock(stmt.body, depth + 1) .. "\n" .. pad .. "until " .. cond
    end

    if kind == AstKind.ReturnStatement then
        if #stmt.args == 0 then
            return pad .. "return"
        end
        return pad .. "return " .. self:formatArgs(stmt.args, depth)
    end

    if kind == AstKind.ForStatement then
        local varName = stmt.scope:getVariableName(stmt.id)
        local init = self:formatExpression(stmt.initialValue, depth)
        local limit = self:formatExpression(stmt.finalValue, depth)
        local header = pad .. "for " .. varName .. " = " .. init .. ", " .. limit
        if stmt.incrementBy and not (stmt.incrementBy.kind == AstKind.NumberExpression and stmt.incrementBy.value == 1) then
            header = header .. ", " .. self:formatExpression(stmt.incrementBy, depth)
        end
        header = header .. " do"
        if #stmt.body.statements == 0 then
            return header .. " end"
        end
        return header .. "\n" .. self:formatBlock(stmt.body, depth + 1) .. "\n" .. pad .. "end"
    end

    if kind == AstKind.ForInStatement then
        local vars = {}
        for i = 1, #stmt.ids do
            vars[i] = stmt.scope:getVariableName(stmt.ids[i])
        end
        local exprs = self:formatArgs(stmt.expressions, depth)
        local header = pad .. "for " .. table.concat(vars, ", ") .. " in " .. exprs .. " do"
        if #stmt.body.statements == 0 then
            return header .. " end"
        end
        return header .. "\n" .. self:formatBlock(stmt.body, depth + 1) .. "\n" .. pad .. "end"
    end

    if kind == AstKind.IfStatement then
        local lines = {}
        lines[#lines + 1] = pad .. "if " .. self:formatExpression(stmt.condition, depth) .. " then"
        if #stmt.body.statements > 0 then
            lines[#lines + 1] = self:formatBlock(stmt.body, depth + 1)
        end
        for i = 1, #stmt.elseifs do
            local eif = stmt.elseifs[i]
            lines[#lines + 1] = pad .. "elseif " .. self:formatExpression(eif.condition, depth) .. " then"
            if #eif.body.statements > 0 then
                lines[#lines + 1] = self:formatBlock(eif.body, depth + 1)
            end
        end
        if stmt.elsebody and #stmt.elsebody.statements > 0 then
            lines[#lines + 1] = pad .. "else"
            lines[#lines + 1] = self:formatBlock(stmt.elsebody, depth + 1)
        end
        lines[#lines + 1] = pad .. "end"
        return table.concat(lines, "\n")
    end

    if kind == AstKind.LocalFunctionDeclaration then
        local name = stmt.scope:getVariableName(stmt.id)
        local params = self:formatParams(stmt.args)
        if #stmt.body.statements == 0 then
            return pad .. "local function " .. name .. "(" .. params .. ") end"
        end
        return pad .. "local function " .. name .. "(" .. params .. ")\n"
            .. self:formatBlock(stmt.body, depth + 1) .. "\n"
            .. pad .. "end"
    end

    if kind == AstKind.FunctionDeclaration then
        local nameParts = { stmt.scope:getVariableName(stmt.id) }
        if stmt.indices then
            for i = 1, #stmt.indices do
                nameParts[#nameParts + 1] = stmt.indices[i]
            end
        end
        local fullName = table.concat(nameParts, ".")
        local params = self:formatParams(stmt.args)
        if #stmt.body.statements == 0 then
            return pad .. "function " .. fullName .. "(" .. params .. ") end"
        end
        return pad .. "function " .. fullName .. "(" .. params .. ")\n"
            .. self:formatBlock(stmt.body, depth + 1) .. "\n"
            .. pad .. "end"
    end

    if kind == AstKind.LocalVariableDeclaration then
        local names = {}
        for i = 1, #stmt.ids do
            names[i] = stmt.scope:getVariableName(stmt.ids[i])
        end
        local code = pad .. "local " .. table.concat(names, ", ")
        if stmt.expressions and #stmt.expressions > 0 then
            code = code .. " = " .. self:formatArgs(stmt.expressions, depth)
        end
        return code
    end

    if kind == AstKind.AssignmentStatement then
        local lhs = {}
        for i = 1, #stmt.lhs do
            lhs[i] = self:formatLhs(stmt.lhs[i], depth)
        end
        return pad .. table.concat(lhs, ", ") .. " = " .. self:formatArgs(stmt.rhs, depth)
    end

    if kind == AstKind.FunctionCallStatement then
        local base = self:formatBase(stmt.base, depth)
        return pad .. base .. "(" .. self:formatArgs(stmt.args, depth) .. ")"
    end

    if kind == AstKind.PassSelfFunctionCallStatement then
        local base = self:formatBase(stmt.base, depth)
        return pad .. base .. ":" .. stmt.passSelfFunctionName .. "(" .. self:formatArgs(stmt.args, depth) .. ")"
    end

    local compound = COMPOUND_OPS[kind]
    if compound then
        if self.luaVersion == LuaVersion.LuaU then
            return pad .. self:formatLhs(stmt.lhs, depth) .. " " .. compound.op .. " " .. self:formatExpression(stmt.rhs, depth)
        end
        if stmt.lhs.kind == AstKind.AssignmentVariable then
            local readExpr = Ast.VariableExpression(stmt.lhs.scope, stmt.lhs.id)
            local binExpr = compound.bin(readExpr, stmt.rhs, false)
            return pad .. self:formatLhs(stmt.lhs, depth) .. " = " .. self:formatExpression(binExpr, depth)
        end
        local p1 = self:pad(depth + 1)
        local binSym = string.sub(compound.op, 1, #compound.op - 1)
        local rhsText = self:formatExpression(stmt.rhs, depth + 1)
        if self:exprPrecedence(stmt.rhs) <= BINARY_OPS[compound.bin(Ast.NumberExpression(0), Ast.NumberExpression(0), false).kind].prec and not stmt.rhs.isParenthesizedExpression then
            rhsText = "(" .. rhsText .. ")"
        end
        return pad .. "do\n"
            .. p1 .. "local _t, _k = " .. self:formatExpression(stmt.lhs.base, depth + 1) .. ", " .. self:formatExpression(stmt.lhs.index, depth + 1) .. "\n"
            .. p1 .. "_t[_k] = _t[_k] " .. binSym .. " " .. rhsText .. "\n"
            .. pad .. "end"
    end

    error("Unsupported statement kind: " .. tostring(kind))
end

function Formatter:formatBlock(block, depth)
    depth = depth or 0
    local stmts = block.statements
    if #stmts == 0 then
        return ""
    end
    local lines = {}
    for i = 1, #stmts do
        local text = self:formatStatement(stmts[i], depth)
        local trimmed = string.match(text, "^%s*(.*)$") or ""
        if i > 1 and string.sub(trimmed, 1, 1) == "(" then
            lines[i - 1] = lines[i - 1] .. ";"
        end
        lines[i] = text
    end
    return table.concat(lines, "\n")
end

function Formatter:format(ast)
    if ast.kind == AstKind.TopNode then
        local out = self:formatBlock(ast.body, 0)
        if #out == 0 then
            return "\n"
        end
        return out .. "\n"
    end
    if ast.kind == AstKind.Block then
        return self:formatBlock(ast, 0)
    end
    return self:formatExpression(ast, 0)
end

return Formatter

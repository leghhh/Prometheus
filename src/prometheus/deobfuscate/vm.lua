local Ast = require("prometheus.ast")
local Scope = require("prometheus.scope")
local Enums = require("prometheus.enums")
local visitast = require("prometheus.visitast")
local util = require("prometheus.util")

local AstKind = Ast.AstKind
local LuaVersion = Enums.LuaVersion
local lookupify = util.lookupify

local VmDecompiler = {}

local function varKey(scope, id)
    return tostring(scope) .. ":" .. tostring(id)
end

local function isVarRef(node, scope, id)
    return node and node.kind == AstKind.VariableExpression and node.scope == scope and node.id == id
end

local function visitSub(node, previsit, postvisit, globalScope)
    if node.kind == AstKind.TopNode then
        return visitast(node, previsit, postvisit)
    end
    local gs = globalScope
    if not gs then
        local sc = node.scope or (node.body and node.body.scope)
        while sc and sc.parentScope do sc = sc.parentScope end
        gs = sc
    end
    if node.kind == AstKind.Block then
        return visitast(Ast.TopNode(node, gs), previsit, postvisit)
    end
    if node.isStatement then
        local blk = Ast.Block({ node }, node.scope or gs)
        visitast(Ast.TopNode(blk, gs), previsit, postvisit)
        return blk.statements[1]
    end
    local ret = Ast.ReturnStatement({ node })
    local blk = Ast.Block({ ret }, gs)
    visitast(Ast.TopNode(blk, gs), previsit, postvisit)
    return ret.args[1]
end

local function evalConstExpr(expr)
    if expr.kind == AstKind.NumberExpression
        or expr.kind == AstKind.StringExpression
        or expr.kind == AstKind.BooleanExpression then
        return true, expr.value
    end
    if expr.kind == AstKind.NilExpression then
        return true, nil
    end
    if expr.kind == AstKind.NegateExpression then
        local ok, v = evalConstExpr(expr.rhs)
        if ok and type(v) == "number" then
            return true, (v == 0) and (-tonumber("0")) or (-v)
        end
    end
    if expr.kind == AstKind.DivExpression then
        local ok1, a = evalConstExpr(expr.lhs)
        local ok2, b = evalConstExpr(expr.rhs)
        if ok1 and ok2 and type(a) == "number" and type(b) == "number" then
            if a == 0 and b == 0 then return true, 0 / 0 end
            if b ~= 0 then return true, a / b end
        end
    end
    return false, nil
end

local function parseNumberArray(tblExpr)
    if tblExpr.kind ~= AstKind.TableConstructorExpression then return nil end
    local out = {}
    for i = 1, #tblExpr.entries do
        local e = tblExpr.entries[i]
        if e.kind ~= AstKind.TableEntry then return nil end
        local ok, v = evalConstExpr(e.value)
        if not ok or type(v) ~= "number" then return nil end
        out[i] = v
    end
    return out
end

local function parsePrototypeTable(tblExpr)
    if tblExpr.kind ~= AstKind.TableConstructorExpression then return nil end
    local fields = {}
    for i = 1, #tblExpr.entries do
        local e = tblExpr.entries[i]
        if e.kind ~= AstKind.KeyedTableEntry or e.key.kind ~= AstKind.StringExpression then
            return nil
        end
        fields[e.key.value] = e.value
    end
    if not fields.code or not fields.constants or not fields.captures
        or not fields.params or not fields.vararg or not fields.children then
        return nil
    end

    local proto = {
        rawCode = {},
        constants = {},
        captures = {},
        params = {},
        vararg = false,
        maxRegister = 0,
        children = {},
    }

    if fields.vararg.kind ~= AstKind.BooleanExpression then return nil end
    proto.vararg = fields.vararg.value

    if fields.maxRegister then
        local ok, mr = evalConstExpr(fields.maxRegister)
        if ok and type(mr) == "number" then proto.maxRegister = mr end
    end

    if fields.code.kind ~= AstKind.TableConstructorExpression then return nil end
    for i = 1, #fields.code.entries do
        local ce = fields.code.entries[i]
        if ce.kind ~= AstKind.TableEntry or ce.value.kind ~= AstKind.TableConstructorExpression then
            return nil
        end
        local row = {}
        for j = 1, #ce.value.entries do
            local se = ce.value.entries[j]
            if se.kind ~= AstKind.TableEntry then return nil end
            if se.value.kind == AstKind.TableConstructorExpression then
                local arr = parseNumberArray(se.value)
                if not arr then return nil end
                row[j] = arr
            else
                local ok, v = evalConstExpr(se.value)
                if not ok then return nil end
                row[j] = v
            end
        end
        proto.rawCode[i] = row
    end

    if fields.constants.kind ~= AstKind.TableConstructorExpression then return nil end
    for i = 1, #fields.constants.entries do
        local ke = fields.constants.entries[i]
        if ke.kind ~= AstKind.TableEntry then return nil end
        local ok, v = evalConstExpr(ke.value)
        if not ok then return nil end
        proto.constants[i] = v
    end

    if fields.captures.kind ~= AstKind.TableConstructorExpression then return nil end
    for i = 1, #fields.captures.entries do
        local ce = fields.captures.entries[i]
        if ce.kind ~= AstKind.TableEntry then return nil end
        local pair = parseNumberArray(ce.value)
        if not pair or #pair ~= 2 then return nil end
        proto.captures[i] = pair
    end

    if fields.params.kind ~= AstKind.TableConstructorExpression then return nil end
    for i = 1, #fields.params.entries do
        local pe = fields.params.entries[i]
        if pe.kind ~= AstKind.TableEntry or pe.value.kind ~= AstKind.TableConstructorExpression or #pe.value.entries ~= 2 then
            return nil
        end
        local e1, e2 = pe.value.entries[1], pe.value.entries[2]
        if e1.kind ~= AstKind.TableEntry or e2.kind ~= AstKind.TableEntry or e2.value.kind ~= AstKind.BooleanExpression then
            return nil
        end
        local ok, reg = evalConstExpr(e1.value)
        if not ok or type(reg) ~= "number" then return nil end
        proto.params[i] = { reg, e2.value.value }
    end

    if fields.children.kind ~= AstKind.TableConstructorExpression then return nil end
    for i = 1, #fields.children.entries do
        local ch = fields.children.entries[i]
        if ch.kind ~= AstKind.TableEntry then return nil end
        local childProto = parsePrototypeTable(ch.value)
        if not childProto then return nil end
        proto.children[i] = childProto
    end

    return proto
end

local BIN_KIND_TO_OP = {
    [AstKind.AddExpression] = "ADD",
    [AstKind.SubExpression] = "SUB",
    [AstKind.MulExpression] = "MUL",
    [AstKind.DivExpression] = "DIV",
    [AstKind.ModExpression] = "MOD",
    [AstKind.PowExpression] = "POW",
    [AstKind.StrCatExpression] = "CONCAT",
    [AstKind.EqualsExpression] = "EQ",
    [AstKind.NotEqualsExpression] = "NE",
    [AstKind.LessThanExpression] = "LT",
    [AstKind.LessThanOrEqualsExpression] = "LE",
    [AstKind.GreaterThanExpression] = "GT",
    [AstKind.GreaterThanOrEqualsExpression] = "GE",
}

local UNARY_KIND_TO_OP = {
    [AstKind.NegateExpression] = "UNM",
    [AstKind.NotExpression] = "NOT",
    [AstKind.LenExpression] = "LEN",
}

local function extractLayout(vmRuntime, globalScope)
    local loopFn = nil
    visitSub(vmRuntime, function(n)
        if (n.kind == AstKind.LocalFunctionDeclaration or n.kind == AstKind.FunctionLiteralExpression)
            and #n.args == 5 then
            local allVars = true
            for i = 1, 5 do
                if n.args[i].kind ~= AstKind.VariableExpression then allVars = false break end
            end
            if allVars then
                loopFn = n
            end
        end
    end, nil, globalScope)

    if not loopFn then return nil end

    local pVar = loopFn.args[1]
    local uVar = loopFn.args[2]
    local envVar = loopFn.args[3]
    local rVar = loopFn.args[4]
    local vVar = loopFn.args[5]
    local afterWhileBlock = nil
    for tsIdx, ts in ipairs(loopFn.body.statements) do
        if ts.kind == AstKind.WhileStatement then
            if tsIdx < #loopFn.body.statements then
                local tail = {}
                for m = tsIdx + 1, #loopFn.body.statements do
                    tail[#tail + 1] = loopFn.body.statements[m]
                end
                afterWhileBlock = Ast.Block(tail, loopFn.body.scope)
            end
            break
        end
        if ts.kind == AstKind.AssignmentStatement and #ts.lhs == 1 and #ts.rhs == 1
            and ts.lhs[1].kind == AstKind.AssignmentVariable and ts.rhs[1].kind == AstKind.VariableExpression then
            local rv, lv = ts.rhs[1], ts.lhs[1]
            if isVarRef(rv, pVar.scope, pVar.id) then pVar = lv
            elseif isVarRef(rv, uVar.scope, uVar.id) then uVar = lv
            elseif isVarRef(rv, envVar.scope, envVar.id) then envVar = lv
            elseif isVarRef(rv, rVar.scope, rVar.id) then rVar = lv
            elseif isVarRef(rv, vVar.scope, vVar.id) then vVar = lv
            end
        end
    end

    local kKey, codeKey, pcKey, instrKey, opKey
    local slotByVar = {}

    visitSub(loopFn.body, function(n)
        if n.kind == AstKind.LocalVariableDeclaration then
            for i = 1, #n.ids do
                local expr = n.expressions and n.expressions[i]
                if expr then
                    local vk = varKey(n.scope, n.ids[i])
                    if expr.kind == AstKind.IndexExpression and isVarRef(expr.base, pVar.scope, pVar.id)
                        and expr.index.kind == AstKind.StringExpression then
                        if expr.index.value == "constants" then kKey = vk end
                        if expr.index.value == "code" then codeKey = vk end
                    elseif expr.kind == AstKind.NumberExpression and expr.value == 1 and not pcKey then
                        pcKey = vk
                    end
                end
            end
        elseif n.kind == AstKind.AssignmentStatement then
            for i = 1, #n.lhs do
                local lhs = n.lhs[i]
                local expr = n.rhs[i]
                if lhs.kind == AstKind.AssignmentVariable and expr then
                    local vk = varKey(lhs.scope, lhs.id)
                    if expr.kind == AstKind.IndexExpression and isVarRef(expr.base, pVar.scope, pVar.id)
                        and expr.index.kind == AstKind.StringExpression then
                        if expr.index.value == "constants" then kKey = vk end
                        if expr.index.value == "code" then codeKey = vk end
                    elseif expr.kind == AstKind.NumberExpression and expr.value == 1 and not pcKey then
                        pcKey = vk
                    end
                end
            end
        end
    end, nil, globalScope)

    visitSub(loopFn.body, function(n)
        if n.kind == AstKind.LocalVariableDeclaration then
            for i = 1, #n.ids do
                local expr = n.expressions and n.expressions[i]
                if expr and expr.kind == AstKind.IndexExpression and expr.base.kind == AstKind.VariableExpression then
                    if varKey(expr.base.scope, expr.base.id) == codeKey then
                        instrKey = varKey(n.scope, n.ids[i])
                        if expr.index.kind == AstKind.VariableExpression then
                            pcKey = varKey(expr.index.scope, expr.index.id)
                        end
                    end
                end
            end
        elseif n.kind == AstKind.AssignmentStatement then
            for i = 1, #n.lhs do
                local lhs = n.lhs[i]
                local expr = n.rhs[i]
                if lhs.kind == AstKind.AssignmentVariable and expr and expr.kind == AstKind.IndexExpression
                    and expr.base.kind == AstKind.VariableExpression
                    and varKey(expr.base.scope, expr.base.id) == codeKey then
                    instrKey = varKey(lhs.scope, lhs.id)
                    if expr.index.kind == AstKind.VariableExpression then
                        pcKey = varKey(expr.index.scope, expr.index.id)
                    end
                end
            end
        end
    end, nil, globalScope)

    if not instrKey then return nil end

    visitSub(loopFn.body, function(n)
        if n.kind == AstKind.LocalVariableDeclaration then
            for i = 1, #n.ids do
                local expr = n.expressions and n.expressions[i]
                if expr and expr.kind == AstKind.IndexExpression
                    and expr.base.kind == AstKind.VariableExpression
                    and varKey(expr.base.scope, expr.base.id) == instrKey
                    and expr.index.kind == AstKind.NumberExpression then
                    local s = expr.index.value
                    local vk = varKey(n.scope, n.ids[i])
                    if s == 1 then
                        opKey = vk
                    elseif s >= 2 and s <= 5 then
                        slotByVar[vk] = s
                    end
                end
            end
        elseif n.kind == AstKind.AssignmentStatement then
            for i = 1, #n.lhs do
                local lhs = n.lhs[i]
                local expr = n.rhs[i]
                if lhs.kind == AstKind.AssignmentVariable and expr and expr.kind == AstKind.IndexExpression
                    and expr.base.kind == AstKind.VariableExpression
                    and varKey(expr.base.scope, expr.base.id) == instrKey
                    and expr.index.kind == AstKind.NumberExpression then
                    local s = expr.index.value
                    local vk = varKey(lhs.scope, lhs.id)
                    if s == 1 then
                        opKey = vk
                    elseif s >= 2 and s <= 5 then
                        slotByVar[vk] = s
                    end
                end
            end
        end
    end, nil, globalScope)

    local function getSlot(expr)
        if not expr then return nil end
        if expr.kind == AstKind.VariableExpression then
            return slotByVar[varKey(expr.scope, expr.id)]
        end
        if expr.kind == AstKind.IndexExpression
            and expr.base.kind == AstKind.VariableExpression
            and varKey(expr.base.scope, expr.base.id) == instrKey
            and expr.index.kind == AstKind.NumberExpression then
            local s = expr.index.value
            if s >= 2 and s <= 5 then return s end
        end
        return nil
    end

    local function isOpExpr(expr)
        if not expr then return false end
        if opKey and expr.kind == AstKind.VariableExpression and varKey(expr.scope, expr.id) == opKey then
            return true
        end
        if expr.kind == AstKind.IndexExpression and expr.base.kind == AstKind.VariableExpression
            and varKey(expr.base.scope, expr.base.id) == instrKey
            and expr.index.kind == AstKind.NumberExpression and expr.index.value == 1 then
            return true
        end
        return false
    end

    local function matchOpEqId(cond)
        if cond.kind == AstKind.EqualsExpression then
            if isOpExpr(cond.lhs) and cond.rhs.kind == AstKind.NumberExpression then
                return cond.rhs.value, false
            elseif isOpExpr(cond.rhs) and cond.lhs.kind == AstKind.NumberExpression then
                return cond.lhs.value, false
            end
        elseif cond.kind == AstKind.NotEqualsExpression then
            if isOpExpr(cond.lhs) and cond.rhs.kind == AstKind.NumberExpression then
                return cond.rhs.value, true
            elseif isOpExpr(cond.rhs) and cond.lhs.kind == AstKind.NumberExpression then
                return cond.lhs.value, true
            end
        elseif cond.kind == AstKind.NotExpression and cond.rhs.kind == AstKind.EqualsExpression then
            local eq = cond.rhs
            if isOpExpr(eq.lhs) and eq.rhs.kind == AstKind.NumberExpression then
                return eq.rhs.value, true
            elseif isOpExpr(eq.rhs) and eq.lhs.kind == AstKind.NumberExpression then
                return eq.lhs.value, true
            end
        end
        return nil, false
    end

    local handlers = {}
    local maxId = 0
    visitSub(loopFn.body, function(n)
        if n.kind == AstKind.IfStatement then
            local id, inv = matchOpEqId(n.condition)
            if id and id >= 1 then
                local b = inv and n.elsebody or n.body
                if b then
                    handlers[id] = b
                    if id > maxId then maxId = id end
                end
            end
            for _, eif in ipairs(n.elseifs) do
                local eid, einv = matchOpEqId(eif.condition)
                if eid and eid >= 1 and not einv then
                    handlers[eid] = eif.body
                    if eid > maxId then maxId = eid end
                end
            end
        end
    end, nil, globalScope)

    if maxId < 50 then return nil end

    local function isR(expr)
        return expr and isVarRef(expr, rVar.scope, rVar.id)
    end
    local function isK(expr)
        return expr and expr.kind == AstKind.VariableExpression and varKey(expr.scope, expr.id) == kKey
    end
    local function isU(expr)
        return expr and isVarRef(expr, uVar.scope, uVar.id)
    end
    local function isEnv(expr)
        return expr and isVarRef(expr, envVar.scope, envVar.id)
    end
    local function isV(expr)
        return expr and isVarRef(expr, vVar.scope, vVar.id)
    end
    local function isPcLhs(lhs)
        return lhs and lhs.kind == AstKind.AssignmentVariable and varKey(lhs.scope, lhs.id) == pcKey
    end
    local function isRIndexSlot(expr)
        if expr and expr.kind == AstKind.IndexExpression and isR(expr.base) then
            return getSlot(expr.index)
        end
        return nil
    end

    local opMap = {}
    local nilOrClearIds = {}
    local slotA, slotB, slotC, slotD

    for id = 1, maxId do
        local body = handlers[id]
        if not body then return nil end
        local stmts = body.statements
        if afterWhileBlock then
            local lastNonNil = nil
            for _, cs in ipairs(stmts) do
                if not (cs.kind == AstKind.AssignmentStatement and #cs.lhs == 1 and #cs.rhs == 1
                    and cs.lhs[1].kind == AstKind.AssignmentVariable
                    and cs.rhs[1].kind == AstKind.NilExpression) then
                    lastNonNil = cs
                end
            end
            if lastNonNil and lastNonNil.kind == AstKind.BreakStatement then
                body = afterWhileBlock
                stmts = body.statements
            end
        end
        local classified = nil

        if #stmts == 1 then
            local s = stmts[1]
            if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1 then
                local lhs, rhs = s.lhs[1], s.rhs[1]
                if isPcLhs(lhs) then
                    local sl = getSlot(rhs)
                    if sl then
                        classified = "JMP"
                        slotA = sl
                    end
                elseif lhs.kind == AstKind.AssignmentIndexing then
                    if isR(lhs.base) then
                        local sa = getSlot(lhs.index)
                        if sa then
                            if rhs.kind == AstKind.NilExpression then
                                classified = "NIL_OR_CLEAR"
                                nilOrClearIds[#nilOrClearIds + 1] = id
                            elseif rhs.kind == AstKind.TableConstructorExpression and #rhs.entries == 0 then
                                classified = "TABLE"
                            elseif isV(rhs) then
                                classified = "VARARG"
                            elseif isRIndexSlot(rhs) then
                                classified = "MOVE"
                            elseif rhs.kind == AstKind.IndexExpression then
                                if isK(rhs.base) then
                                    local sb = getSlot(rhs.index)
                                    if sb then
                                        classified = "LOAD"
                                        slotA = slotA or sa
                                        slotB = sb
                                    end
                                elseif isEnv(rhs.base) and rhs.index.kind == AstKind.IndexExpression and isK(rhs.index.base) then
                                    classified = "GLOBAL"
                                elseif rhs.index.kind == AstKind.NumberExpression and rhs.index.value == 1 then
                                    if isRIndexSlot(rhs.base) then
                                        classified = "GETCELL"
                                    elseif rhs.base.kind == AstKind.IndexExpression and isU(rhs.base.base) then
                                        classified = "GETUP"
                                    end
                                elseif isRIndexSlot(rhs.base) then
                                    local sc = isRIndexSlot(rhs.index)
                                    if sc then
                                        classified = "GETTABLE"
                                        slotC = sc
                                    elseif getSlot(rhs.index) then
                                        classified = "TAKE"
                                    end
                                end
                            elseif BIN_KIND_TO_OP[rhs.kind] then
                                classified = BIN_KIND_TO_OP[rhs.kind]
                            elseif UNARY_KIND_TO_OP[rhs.kind] then
                                classified = UNARY_KIND_TO_OP[rhs.kind]
                            end
                        end
                    elseif lhs.base.kind == AstKind.IndexExpression then
                        if isRIndexSlot(lhs.base) and isRIndexSlot(lhs.index) then
                            classified = "SETTABLE"
                        elseif isR(lhs.base.base) and lhs.index.kind == AstKind.NumberExpression and lhs.index.value == 1 then
                            classified = "SETCELL"
                        elseif isU(lhs.base.base) and lhs.index.kind == AstKind.NumberExpression and lhs.index.value == 1 then
                            classified = "SETUP"
                        end
                    elseif isEnv(lhs.base) then
                        classified = "SETGLOBAL"
                    end
                end
            elseif s.kind == AstKind.ForStatement then
                classified = "CLEARS"
            elseif s.kind == AstKind.ReturnStatement then
                if #s.args == 0 then classified = "RETURN0"
                elseif #s.args == 1 then classified = "RETURN1"
                elseif #s.args == 2 then classified = "RETURN2"
                elseif #s.args == 3 then classified = "RETURN3"
                end
            elseif s.kind == AstKind.IfStatement and s.condition.kind == AstKind.NotEqualsExpression then
                local sd = isRIndexSlot(s.condition.lhs)
                if sd and sd == isRIndexSlot(s.condition.rhs) then
                    classified = "FORCHECK"
                    slotD = sd
                end
            end
        elseif #stmts == 2 then
            local s1, s2 = stmts[1], stmts[2]
            if s2.kind == AstKind.ReturnStatement and #s2.args == 1
                and s2.args[1].kind == AstKind.FunctionCallExpression then
                classified = "RETURN"
            elseif s2.kind == AstKind.ForStatement then
                classified = "EXPAND"
            elseif s2.kind == AstKind.AssignmentStatement and #s2.rhs == 1
                and s2.rhs[1].kind == AstKind.TableConstructorExpression and #s2.rhs[1].entries == 1 then
                classified = "CELL"
            elseif s1.kind == AstKind.AssignmentStatement and s2.kind == AstKind.IfStatement then
                if #s1.lhs == 2 then
                    classified = "CALL"
                elseif #s1.lhs == 1 and s2.elsebody and #s2.elsebody.statements == 1
                    and s2.elsebody.statements[1].kind == AstKind.FunctionCallStatement then
                    classified = "CALL" .. tostring(#s2.elsebody.statements[1].args)
                end
            end
        elseif #stmts == 3 then
            local s1, s3 = stmts[1], stmts[3]
            if s3.kind == AstKind.IfStatement then
                if s3.condition.kind == AstKind.NotExpression then
                    classified = "JFALSE"
                else
                    classified = "JTRUE"
                end
            elseif s3.kind == AstKind.ReturnStatement and #s3.args == 1
                and s3.args[1].kind == AstKind.FunctionCallExpression then
                if s1.kind == AstKind.AssignmentStatement and #s1.lhs == 2 then
                    classified = "TAILCALL"
                elseif s1.kind == AstKind.AssignmentStatement and #s1.lhs == 1 then
                    classified = "TAILCALL" .. tostring(#s3.args[1].args)
                end
            end
        elseif #stmts == 4 then
            if stmts[2].kind == AstKind.ForInStatement then
                classified = "ARGS"
            elseif stmts[3].kind == AstKind.ForStatement then
                classified = "CLOSURE"
            end
        end

        if not classified then
            local core = {}
            for _, cs in ipairs(stmts) do
                if not (cs.kind == AstKind.AssignmentStatement and #cs.lhs == 1 and #cs.rhs == 1
                    and cs.lhs[1].kind == AstKind.AssignmentVariable
                    and cs.rhs[1].kind == AstKind.NilExpression) then
                    core[#core + 1] = cs
                end
            end

            local hasChildrenStr = false
            local hasForPrepErr = false
            local hasNZeroTbl = false
            local hasNOneTbl = false
            local hasSingleElemTbl = false
            local hasEmptyTbl = false
            local hasWhileOrFor = false
            local hasSelfNe = nil
            local retList = {}
            local callStmtArgs = nil
            local hasUnpackCall = false
            local pcAssignInIf = false
            local pcIfHasNot = false

            local nFieldVars = {}
            visitSub(body, function(n)
                if n.kind == AstKind.AssignmentStatement and #n.lhs == 1 and #n.rhs == 1
                    and n.lhs[1].kind == AstKind.AssignmentVariable
                    and n.rhs[1].kind == AstKind.IndexExpression
                    and n.rhs[1].index.kind == AstKind.StringExpression
                    and n.rhs[1].index.value == "n" then
                    nFieldVars[varKey(n.lhs[1].scope, n.lhs[1].id)] = true
                end
            end, nil, globalScope)

            local calleeKey = nil
            if #core >= 1 and core[1].kind == AstKind.AssignmentStatement
                and #core[1].lhs >= 1 and #core[1].rhs >= 1
                and core[1].lhs[1].kind == AstKind.AssignmentVariable
                and isRIndexSlot(core[1].rhs[1]) then
                calleeKey = varKey(core[1].lhs[1].scope, core[1].lhs[1].id)
            end
            local calleeArity = nil

            visitSub(body, function(n)
                if n.kind == AstKind.StringExpression then
                    if n.value == "children" then hasChildrenStr = true end
                    if string.find(n.value, "initial value must be a number", 1, true) then hasForPrepErr = true end
                elseif n.kind == AstKind.TableConstructorExpression then
                    if #n.entries == 0 then
                        hasEmptyTbl = true
                    elseif #n.entries == 1 and n.entries[1].kind == AstKind.TableEntry then
                        hasSingleElemTbl = true
                    else
                        for _, ent in ipairs(n.entries) do
                            if ent.kind == AstKind.KeyedTableEntry
                                and ent.key.kind == AstKind.StringExpression and ent.key.value == "n"
                                and ent.value.kind == AstKind.NumberExpression then
                                if ent.value.value == 0 then hasNZeroTbl = true end
                                if ent.value.value == 1 then hasNOneTbl = true end
                            end
                        end
                    end
                elseif n.kind == AstKind.WhileStatement or n.kind == AstKind.ForStatement or n.kind == AstKind.ForInStatement then
                    hasWhileOrFor = true
                elseif n.kind == AstKind.NotEqualsExpression then
                    local sd1 = isRIndexSlot(n.lhs)
                    local sd2 = isRIndexSlot(n.rhs)
                    if sd1 and sd1 == sd2 then hasSelfNe = sd1 end
                elseif n.kind == AstKind.ReturnStatement then
                    retList[#retList + 1] = n
                elseif n.kind == AstKind.FunctionCallExpression then
                    if #n.args == 3 and n.args[2].kind == AstKind.NumberExpression and n.args[2].value == 1 then
                        local a3 = n.args[3]
                        if (a3.kind == AstKind.IndexExpression and a3.index.kind == AstKind.StringExpression and a3.index.value == "n")
                            or (a3.kind == AstKind.VariableExpression and nFieldVars[varKey(a3.scope, a3.id)]) then
                            hasUnpackCall = true
                        end
                    end
                    if calleeKey and n.base.kind == AstKind.VariableExpression
                        and varKey(n.base.scope, n.base.id) == calleeKey then
                        calleeArity = #n.args
                    end
                elseif n.kind == AstKind.FunctionCallStatement then
                    callStmtArgs = #n.args
                    if calleeKey and n.base.kind == AstKind.VariableExpression
                        and varKey(n.base.scope, n.base.id) == calleeKey then
                        calleeArity = #n.args
                    end
                elseif n.kind == AstKind.IfStatement then
                    local hasPc = false
                    visitSub(n, function(m)
                        if m.kind == AstKind.AssignmentStatement and #m.lhs == 1 and isPcLhs(m.lhs[1]) then
                            hasPc = true
                        end
                    end, nil, globalScope)
                    if hasPc then
                        pcAssignInIf = true
                        if n.condition.kind == AstKind.NotExpression then
                            pcIfHasNot = true
                        end
                    end
                end
            end, nil, globalScope)

            if hasChildrenStr then
                classified = "CLOSURE"
            elseif hasNZeroTbl then
                classified = "ARGS"
            elseif hasForPrepErr and not hasWhileOrFor then
                classified = "FORPREP"
            elseif hasSelfNe then
                classified = "FORCHECK"
                slotD = slotD or hasSelfNe
            elseif hasNOneTbl then
                if hasUnpackCall then
                    classified = "CALL"
                elseif calleeArity ~= nil then
                    classified = "CALL" .. tostring(calleeArity)
                elseif callStmtArgs ~= nil then
                    classified = "CALL" .. tostring(callStmtArgs)
                end
            elseif #retList >= 2 then
                if hasUnpackCall then
                    classified = "TAILCALL"
                elseif calleeArity ~= nil then
                    classified = "TAILCALL" .. tostring(calleeArity)
                else
                    for _, rn in ipairs(retList) do
                        if #rn.args == 1 and rn.args[1].kind == AstKind.FunctionCallExpression then
                            classified = "TAILCALL" .. tostring(#rn.args[1].args)
                        end
                    end
                end
            elseif #retList == 1 then
                local rn = retList[1]
                if #rn.args == 0 then classified = "RETURN0"
                elseif #rn.args == 2 then classified = "RETURN2"
                elseif #rn.args == 3 then classified = "RETURN3"
                elseif #rn.args == 1 then
                    if hasUnpackCall then
                        classified = "RETURN"
                    else
                        classified = "RETURN1"
                    end
                end
            elseif pcAssignInIf then
                classified = pcIfHasNot and "JFALSE" or "JTRUE"
            elseif hasWhileOrFor then
                local hasDirectRWrite = false
                visitSub(body, function(n)
                    if n.kind == AstKind.AssignmentStatement and #n.lhs == 1 and #n.rhs == 1
                        and n.lhs[1].kind == AstKind.AssignmentIndexing and isR(n.lhs[1].base) then
                        hasDirectRWrite = true
                    end
                end, nil, globalScope)
                classified = hasDirectRWrite and "CLEARS" or "EXPAND"
            elseif hasSingleElemTbl and not hasWhileOrFor then
                classified = "CELL"
            elseif #core >= 1 then
                local regVal = {}
                for _, cs in ipairs(stmts) do
                    if cs == core[#core] then break end
                    if cs.kind == AstKind.AssignmentStatement and #cs.lhs == 1 and #cs.rhs == 1 then
                        local lhs, rhs = cs.lhs[1], cs.rhs[1]
                        if lhs.kind == AstKind.AssignmentVariable then
                            regVal[varKey(lhs.scope, lhs.id)] = rhs
                        end
                    end
                end
                local function expandTemps(e, depth)
                    if not e or depth > 6 then return e end
                    if e.kind == AstKind.VariableExpression then
                        local v = regVal[varKey(e.scope, e.id)]
                        if v then return expandTemps(v, depth + 1) end
                        return e
                    elseif e.kind == AstKind.IndexExpression then
                        return Ast.IndexExpression(expandTemps(e.base, depth + 1), expandTemps(e.index, depth + 1))
                    elseif BIN_KIND_TO_OP[e.kind] then
                        local ctor = {
                            ADD = Ast.AddExpression, SUB = Ast.SubExpression, MUL = Ast.MulExpression,
                            DIV = Ast.DivExpression, MOD = Ast.ModExpression, POW = Ast.PowExpression,
                            CONCAT = Ast.StrCatExpression, EQ = Ast.EqualsExpression, NE = Ast.NotEqualsExpression,
                            LT = Ast.LessThanExpression, LE = Ast.LessThanOrEqualsExpression,
                            GT = Ast.GreaterThanExpression, GE = Ast.GreaterThanOrEqualsExpression,
                        }
                        return ctor[BIN_KIND_TO_OP[e.kind]](expandTemps(e.lhs, depth + 1), expandTemps(e.rhs, depth + 1))
                    elseif UNARY_KIND_TO_OP[e.kind] then
                        local uctor = {
                            UNM = Ast.NegateExpression, NOT = Ast.NotExpression, LEN = Ast.LenExpression,
                        }
                        return uctor[UNARY_KIND_TO_OP[e.kind]](expandTemps(e.rhs, depth + 1))
                    end
                    return e
                end
                local lastS = core[#core]
                if lastS.kind == AstKind.AssignmentStatement and #lastS.lhs == 1 and #lastS.rhs == 1 then
                    local lhs = lastS.lhs[1]
                    local rhs = expandTemps(lastS.rhs[1], 0)
                    if isPcLhs(lhs) then
                        local sl = getSlot(rhs)
                        if sl then
                            classified = "JMP"
                            slotA = slotA or sl
                        end
                    elseif lhs.kind == AstKind.AssignmentIndexing then
                        local lb = expandTemps(lhs.base, 0)
                        local li = expandTemps(lhs.index, 0)
                        if isR(lb) then
                            local sa = getSlot(li)
                            if sa then
                                if rhs.kind == AstKind.NilExpression then
                                    classified = "NIL_OR_CLEAR"
                                    nilOrClearIds[#nilOrClearIds + 1] = id
                                elseif (rhs.kind == AstKind.TableConstructorExpression and #rhs.entries == 0) or hasEmptyTbl then
                                    classified = "TABLE"
                                elseif isV(rhs) then
                                    classified = "VARARG"
                                elseif isRIndexSlot(rhs) then
                                    classified = "MOVE"
                                elseif rhs.kind == AstKind.IndexExpression then
                                    if isK(rhs.base) then
                                        local sb = getSlot(rhs.index)
                                        if sb then
                                            classified = "LOAD"
                                            slotA = slotA or sa
                                            slotB = slotB or sb
                                        end
                                    elseif isEnv(rhs.base) and rhs.index.kind == AstKind.IndexExpression and isK(rhs.index.base) then
                                        classified = "GLOBAL"
                                    elseif rhs.index.kind == AstKind.NumberExpression and rhs.index.value == 1 then
                                        if isRIndexSlot(rhs.base) then
                                            classified = "GETCELL"
                                        elseif rhs.base.kind == AstKind.IndexExpression and isU(rhs.base.base) then
                                            classified = "GETUP"
                                        end
                                    elseif isRIndexSlot(rhs.base) then
                                        local sc = isRIndexSlot(rhs.index)
                                        if sc then
                                            classified = "GETTABLE"
                                            slotC = slotC or sc
                                        elseif getSlot(rhs.index) then
                                            classified = "TAKE"
                                        end
                                    end
                                elseif BIN_KIND_TO_OP[rhs.kind] then
                                    classified = BIN_KIND_TO_OP[rhs.kind]
                                elseif UNARY_KIND_TO_OP[rhs.kind] then
                                    classified = UNARY_KIND_TO_OP[rhs.kind]
                                end
                            end
                        elseif lb.kind == AstKind.IndexExpression then
                            if isRIndexSlot(lb) and isRIndexSlot(li) then
                                classified = "SETTABLE"
                            elseif isR(lb.base) and li.kind == AstKind.NumberExpression and li.index == nil and li.value == 1 then
                                classified = "SETCELL"
                            elseif isU(lb.base) and li.kind == AstKind.NumberExpression and li.value == 1 then
                                classified = "SETUP"
                            end
                        elseif isEnv(lb) then
                            classified = "SETGLOBAL"
                        end
                    end
                end
            end
        end

        if not classified then
            return nil
        end
        opMap[id] = classified
    end

    if not slotA or not slotB or not slotC then return nil end
    if not slotD then
        local used = { [slotA] = true, [slotB] = true, [slotC] = true }
        for s = 2, 5 do
            if not used[s] then slotD = s break end
        end
    end
    if not slotD or #nilOrClearIds ~= 2 then return nil end

    return {
        opMap = opMap,
        operands = { slotA, slotB, slotC, slotD },
        nilOrClearIds = nilOrClearIds,
    }
end

local function decodePrototypes(rootProto, layout)
    local operands = layout.operands
    local opMap = layout.opMap

    local function walk(proto)
        proto.code = {}
        for pc = 1, #proto.rawCode do
            local raw = proto.rawCode[pc]
            local opId = raw[1]
            proto.code[pc] = {
                opId = opId,
                op = opMap[opId],
                a = raw[operands[1]],
                b = raw[operands[2]],
                c = raw[operands[3]],
                d = raw[operands[4]],
            }
        end
        for i = 1, #proto.children do
            walk(proto.children[i])
        end
    end
    walk(rootProto)

    local id1, id2 = layout.nilOrClearIds[1], layout.nilOrClearIds[2]

    local function insReadsReg(ins, reg)
        local op = ins.op
        if op == "MOVE" or op == "CELL" or op == "GETCELL" or op == "UNM" or op == "NOT" or op == "LEN"
            or op == "SETGLOBAL" or op == "SETUP" or op == "SETCELL" then
            return ins.b == reg
        elseif op == "GETTABLE" or op == "ADD" or op == "SUB" or op == "MUL" or op == "DIV"
            or op == "MOD" or op == "POW" or op == "CONCAT" or op == "EQ" or op == "NE"
            or op == "LT" or op == "LE" or op == "GT" or op == "GE" then
            return ins.b == reg or ins.c == reg
        elseif op == "TAKE" then
            return ins.b == reg
        elseif op == "SETTABLE" then
            return ins.a == reg or ins.b == reg or ins.c == reg
        elseif op == "JTRUE" or op == "JFALSE" or op == "RETURN" or op == "RETURN1" then
            return ins.a == reg
        elseif op == "RETURN2" then
            return ins.a == reg or ins.b == reg
        elseif op == "RETURN3" then
            return ins.a == reg or ins.b == reg or ins.c == reg
        elseif op == "FORPREP" then
            return ins.a == reg or ins.b == reg or ins.c == reg
        elseif op == "FORCHECK" then
            return ins.b == reg or ins.c == reg or ins.d == reg
        elseif op == "ARGS" then
            if type(ins.b) == "table" then
                for i = 1, #ins.b do
                    if ins.b[i] == reg then return true end
                end
            end
            return ins.c ~= 0 and ins.c == reg
        elseif op == "EXPAND" then
            return ins.a == reg or ins.c == reg
        elseif op == "CALL" then
            return ins.b == reg or ins.c == reg
        elseif op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3" then
            if ins.b == reg then return true end
            if type(ins.c) == "table" then
                for i = 1, #ins.c do
                    if ins.c[i] == reg then return true end
                end
            end
            return false
        elseif op == "TAILCALL" then
            return ins.a == reg or ins.b == reg
        elseif op == "TAILCALL0" or op == "TAILCALL1" or op == "TAILCALL2" or op == "TAILCALL3" then
            if ins.a == reg then return true end
            if type(ins.b) == "table" then
                for i = 1, #ins.b do
                    if ins.b[i] == reg then return true end
                end
            end
            return false
        end
        return false
    end

    local function insOverwritesReg(ins, reg)
        local op = ins.op
        if op == "NIL_OR_CLEAR" or op == "LOAD" or op == "MOVE" or op == "GLOBAL"
            or op == "CELL" or op == "GETCELL" or op == "GETUP" or op == "TABLE"
            or op == "GETTABLE" or op == "TAKE" or op == "CLOSURE" or op == "VARARG"
            or op == "ARGS" or op == "FORCHECK"
            or op == "UNM" or op == "NOT" or op == "LEN"
            or op == "ADD" or op == "SUB" or op == "MUL" or op == "DIV"
            or op == "MOD" or op == "POW" or op == "CONCAT"
            or op == "EQ" or op == "NE" or op == "LT" or op == "LE" or op == "GT" or op == "GE" then
            return ins.a == reg
        elseif op == "CLEARS" and type(ins.a) == "table" then
            for i = 1, #ins.a do
                if ins.a[i] == reg then return true end
            end
        elseif (op == "CALL" or op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3") and ins.d ~= 0 then
            return ins.a == reg
        end
        return false
    end

    local hasReadAfter = { [id1] = false, [id2] = false }

    local function checkProto(proto)
        local code = proto.code
        local n = #code
        for pc = 1, n do
            local ins = code[pc]
            if ins.op == "NIL_OR_CLEAR" and not hasReadAfter[ins.opId] then
                local reg = ins.a
                local visited = {}
                local queue = { pc + 1 }
                local qh = 1
                while qh <= #queue do
                    local cur = queue[qh]
                    qh = qh + 1
                    if cur >= 1 and cur <= n and not visited[cur] then
                        visited[cur] = true
                        local ci = code[cur]
                        if insReadsReg(ci, reg) then
                            hasReadAfter[ins.opId] = true
                            break
                        end
                        if not insOverwritesReg(ci, reg) then
                            if ci.op == "JMP" then
                                queue[#queue + 1] = ci.a
                            elseif ci.op == "JTRUE" or ci.op == "JFALSE" then
                                queue[#queue + 1] = ci.b
                                queue[#queue + 1] = cur + 1
                            elseif ci.op ~= "RETURN" and ci.op ~= "RETURN0" and ci.op ~= "RETURN1"
                                and ci.op ~= "RETURN2" and ci.op ~= "RETURN3"
                                and ci.op ~= "TAILCALL" and ci.op ~= "TAILCALL0" and ci.op ~= "TAILCALL1"
                                and ci.op ~= "TAILCALL2" and ci.op ~= "TAILCALL3" then
                                queue[#queue + 1] = cur + 1
                            end
                        end
                    end
                end
            end
        end
        for i = 1, #proto.children do
            checkProto(proto.children[i])
        end
    end
    checkProto(rootProto)

    local function finalizeOps(proto)
        for pc = 1, #proto.code do
            local ins = proto.code[pc]
            if ins.op == "NIL_OR_CLEAR" then
                ins.op = hasReadAfter[ins.opId] and "NIL" or "CLEAR"
            end
        end
        for i = 1, #proto.children do
            finalizeOps(proto.children[i])
        end
    end
    finalizeOps(rootProto)
end

local BIN_AST_CTOR = {
    ADD = Ast.AddExpression,
    SUB = Ast.SubExpression,
    MUL = Ast.MulExpression,
    DIV = Ast.DivExpression,
    MOD = Ast.ModExpression,
    POW = Ast.PowExpression,
    CONCAT = Ast.StrCatExpression,
    EQ = Ast.EqualsExpression,
    NE = Ast.NotEqualsExpression,
    LT = Ast.LessThanExpression,
    LE = Ast.LessThanOrEqualsExpression,
    GT = Ast.GreaterThanExpression,
    GE = Ast.GreaterThanOrEqualsExpression,
}

local UNARY_AST_CTOR = {
    UNM = Ast.NegateExpression,
    NOT = Ast.NotExpression,
    LEN = Ast.LenExpression,
}

local function makeConstExpr(val)
    if val == nil then return Ast.NilExpression() end
    local t = type(val)
    if t == "boolean" then return Ast.BooleanExpression(val) end
    if t == "string" then return Ast.StringExpression(val) end
    if t == "number" then return Ast.NumberExpression(val) end
    error("Invalid constant type: " .. tostring(t))
end

local function isExpandableExpr(expr)
    return expr.kind == AstKind.FunctionCallExpression
        or expr.kind == AstKind.PassSelfFunctionCallExpression
        or expr.kind == AstKind.VarargExpression
end

local function cloneExpr(expr)
    if type(expr) ~= "table" then return expr end
    local out = {}
    for k, v in pairs(expr) do
        if k == "scope" or k == "parentScope" then
            out[k] = v
        elseif type(v) == "table" then
            out[k] = cloneExpr(v)
        else
            out[k] = v
        end
    end
    return out
end

local function isValidIdent(s)
    if type(s) ~= "string" or #s == 0 then return false end
    return string.match(s, "^[A-Za-z_][A-Za-z0-9_]*$") ~= nil
end

local function analyzeProtoRegisters(proto)
    local code = proto.code
    local n = #code
    local info = {}
    local function getInfo(r)
        if not info[r] then
            info[r] = {
                defs = {},
                reads = {},
                clears = {},
                isParam = false,
                isCell = false,
                isCapturedByChild = false,
                isLoopControl = false,
                isLoopVar = false,
            }
        end
        return info[r]
    end

    for i = 1, #proto.params do
        local r, cap = proto.params[i][1], proto.params[i][2]
        local ri = getInfo(r)
        ri.isParam = true
        if cap then ri.isCell = true end
    end

    for i = 1, #proto.children do
        local ch = proto.children[i]
        for u = 1, #ch.captures do
            if ch.captures[u][1] == 0 then
                local r = ch.captures[u][2]
                local ri = getInfo(r)
                ri.isCapturedByChild = true
                ri.isCell = true
            end
        end
    end

    local function addDef(r, pc)
        if type(r) == "number" and r > 0 then
            local t = getInfo(r).defs
            t[#t + 1] = pc
        end
    end
    local function addRead(r, pc)
        if type(r) == "number" and r > 0 then
            local t = getInfo(r).reads
            t[#t + 1] = pc
        end
    end
    local function addClear(r, pc)
        if type(r) == "number" and r > 0 then
            local t = getInfo(r).clears
            t[#t + 1] = pc
        end
    end

    for pc = 1, n do
        local ins = code[pc]
        local op = ins.op
        if op == "CLEAR" then
            addClear(ins.a, pc)
        elseif op == "CLEARS" then
            for i = 1, #ins.a do addClear(ins.a[i], pc) end
        elseif op == "LOAD" or op == "NIL" or op == "GLOBAL" or op == "TABLE" or op == "CLOSURE" or op == "VARARG" then
            addDef(ins.a, pc)
        elseif op == "MOVE" or op == "UNM" or op == "NOT" or op == "LEN" or op == "TAKE" then
            addRead(ins.b, pc)
            addDef(ins.a, pc)
        elseif op == "CELL" then
            addRead(ins.b, pc)
            addDef(ins.a, pc)
            getInfo(ins.a).isCell = true
        elseif op == "GETCELL" then
            addRead(ins.b, pc)
            getInfo(ins.b).isCell = true
            addDef(ins.a, pc)
        elseif op == "SETCELL" then
            addRead(ins.b, pc)
            addDef(ins.a, pc)
            getInfo(ins.a).isCell = true
        elseif op == "GETUP" then
            addDef(ins.a, pc)
        elseif op == "SETUP" or op == "SETGLOBAL" then
            addRead(ins.b, pc)
        elseif op == "GETTABLE" or BIN_AST_CTOR[op] then
            addRead(ins.b, pc)
            addRead(ins.c, pc)
            addDef(ins.a, pc)
        elseif op == "SETTABLE" then
            addRead(ins.a, pc)
            addRead(ins.b, pc)
            addRead(ins.c, pc)
        elseif op == "JTRUE" or op == "JFALSE" or op == "RETURN" or op == "RETURN1" then
            addRead(ins.a, pc)
        elseif op == "RETURN2" then
            addRead(ins.a, pc)
            addRead(ins.b, pc)
        elseif op == "RETURN3" then
            addRead(ins.a, pc)
            addRead(ins.b, pc)
            addRead(ins.c, pc)
        elseif op == "ARGS" then
            for i = 1, #ins.b do addRead(ins.b[i], pc) end
            if ins.c ~= 0 then addRead(ins.c, pc) end
            addDef(ins.a, pc)
        elseif op == "EXPAND" then
            addRead(ins.a, pc)
            addRead(ins.c, pc)
        elseif op == "FORPREP" then
            addRead(ins.a, pc); addRead(ins.b, pc); addRead(ins.c, pc)
            addDef(ins.a, pc); addDef(ins.b, pc); addDef(ins.c, pc)
            getInfo(ins.a).isLoopControl = true
            getInfo(ins.b).isLoopControl = true
            getInfo(ins.c).isLoopControl = true
        elseif op == "FORCHECK" then
            addRead(ins.b, pc); addRead(ins.c, pc); addRead(ins.d, pc)
            addDef(ins.a, pc)
        elseif op == "CALL" then
            addRead(ins.b, pc); addRead(ins.c, pc)
            if ins.d ~= 0 then addDef(ins.a, pc) end
        elseif op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3" then
            addRead(ins.b, pc)
            for i = 1, #ins.c do addRead(ins.c[i], pc) end
            if ins.d ~= 0 then addDef(ins.a, pc) end
        elseif op == "TAILCALL" then
            addRead(ins.a, pc); addRead(ins.b, pc)
        elseif op == "TAILCALL0" or op == "TAILCALL1" or op == "TAILCALL2" or op == "TAILCALL3" then
            addRead(ins.a, pc)
            for i = 1, #ins.b do addRead(ins.b[i], pc) end
        end
    end

    local jumpTargets = {}
    for pc = 1, n do
        local ins = code[pc]
        if ins.op == "JMP" then
            jumpTargets[ins.a] = true
        elseif ins.op == "JTRUE" or ins.op == "JFALSE" then
            jumpTargets[ins.b] = true
            jumpTargets[pc + 1] = true
        end
    end

    local blockIdAt = {}
    local curBlock = 1
    for pc = 1, n do
        if jumpTargets[pc] and pc > 1 then
            curBlock = curBlock + 1
        end
        blockIdAt[pc] = curBlock
        local op = code[pc].op
        if op == "JMP" or op == "JTRUE" or op == "JFALSE"
            or op == "RETURN" or op == "RETURN0" or op == "RETURN1" or op == "RETURN2" or op == "RETURN3"
            or op == "TAILCALL" or op == "TAILCALL0" or op == "TAILCALL1" or op == "TAILCALL2" or op == "TAILCALL3" then
            curBlock = curBlock + 1
        end
    end

    local loopsByStart = {}
    for pc = 1, n do
        local ins = code[pc]
        if ins.op == "JMP" and ins.a <= pc then
            loopsByStart[ins.a] = pc
        end
    end

    return info, blockIdAt, loopsByStart
end

local function liftPrototype(proto, parentLookup, globalScope, targetLuaVersion, isRootChunk)
    local code = proto.code
    local K = proto.constants
    local regInfo, blockIdAt, loopsByStart = analyzeProtoRegisters(proto)

    local funcScope = Scope:new(parentLookup and parentLookup.enclosingScope or globalScope)
    local captures = {}
    for u = 1, #proto.captures do
        local kind, idx = proto.captures[u][1], proto.captures[u][2]
        if kind == 0 then
            captures[u] = parentLookup.getRegBinding(idx)
        else
            captures[u] = parentLookup.captures[idx]
        end
    end

    local paramArgs = {}
    local regBindings = {}

    for i = 1, #proto.params do
        local reg = proto.params[i][1]
        local id = funcScope:addVariable()
        regBindings[reg] = { scope = funcScope, id = id, declared = true, isParam = true }
        paramArgs[#paramArgs + 1] = Ast.VariableExpression(funcScope, id)
    end
    if proto.vararg and not isRootChunk then
        paramArgs[#paramArgs + 1] = Ast.VarargExpression()
    end

    local function matchGenericForHeader(checkPc, backPc)
        if backPc - checkPc < 5 then return nil end
        local i1 = code[checkPc]
        local i2 = code[checkPc + 1]
        local i3 = code[checkPc + 2]
        local i4 = code[checkPc + 3]
        if not (i1 and i1.op == "CALL2" and i1.d == -1 and type(i1.c) == "table" and #i1.c == 2) then
            return nil
        end
        local resultsReg = i1.a
        local iterReg, stateReg, ctrlReg = i1.b, i1.c[1], i1.c[2]
        if not (i2 and i2.op == "TAKE" and i2.b == resultsReg and i2.c == 1) then return nil end
        local firstReg = i2.a
        if not (i3 and i3.op == "NIL") then return nil end
        local nilReg = i3.a
        if not (i4 and i4.op == "EQ" and ((i4.b == firstReg and i4.c == nilReg) or (i4.c == firstReg and i4.b == nilReg))) then
            return nil
        end
        local p = checkPc + 4
        while p < backPc and (code[p].op == "CLEAR" or code[p].op == "CLEARS") do
            p = p + 1
        end
        local i5 = code[p]
        local i6 = code[p + 1]
        if not (i5 and i5.op == "JTRUE" and i5.a == i4.a and i5.b == backPc + 1) then return nil end
        if not (i6 and i6.op == "MOVE" and i6.a == ctrlReg and i6.b == firstReg) then return nil end

        local loopVarRegs = {}
        local loopVarIsCell = {}
        p = p + 2
        while p < backPc and (code[p].op == "CLEAR" or code[p].op == "CLEARS") do
            p = p + 1
        end
        local varIndex = 1
        while p < backPc do
            local tk = code[p]
            if tk.op == "TAKE" and tk.b == resultsReg and tk.c == varIndex then
                local nextIns = code[p + 1]
                if nextIns and (nextIns.op == "MOVE" or nextIns.op == "CELL") and nextIns.b == tk.a then
                    loopVarRegs[varIndex] = nextIns.a
                    loopVarIsCell[varIndex] = (nextIns.op == "CELL")
                    p = p + 2
                else
                    loopVarRegs[varIndex] = tk.a
                    loopVarIsCell[varIndex] = false
                    p = p + 1
                end
                while p < backPc and (code[p].op == "CLEAR" or code[p].op == "CLEARS") do
                    p = p + 1
                end
                varIndex = varIndex + 1
            else
                break
            end
        end
        if #loopVarRegs == 0 then return nil end
        while p < backPc and (code[p].op == "CLEAR" or code[p].op == "CLEARS") do
            p = p + 1
        end
        return {
            iterReg = iterReg,
            stateReg = stateReg,
            ctrlReg = ctrlReg,
            loopVarRegs = loopVarRegs,
            loopVarIsCell = loopVarIsCell,
            bodyStart = p,
            bodyEnd = backPc - 1,
            endPos = backPc + 1,
            continueTarget = backPc,
        }
    end

    local function matchNumericForHeader(prepPc)
        local prep = code[prepPc]
        if not prep or prep.op ~= "FORPREP" then return nil end
        local checkPc = prepPc + 1
        local backPc = loopsByStart[checkPc]
        if not backPc then return nil end
        local fc = code[checkPc]
        local jf = code[checkPc + 1]
        local iv = code[checkPc + 2]
        if not (fc and fc.op == "FORCHECK" and fc.b == prep.a and fc.c == prep.b and fc.d == prep.c) then
            return nil
        end
        if not (jf and jf.op == "JFALSE" and jf.a == fc.a and jf.b == backPc + 1) then
            return nil
        end
        if not (iv and (iv.op == "MOVE" or iv.op == "CELL") and iv.b == prep.a) then
            return nil
        end
        local advStart = nil
        if backPc - 1 >= checkPc + 3
            and code[backPc - 1].op == "ADD"
            and code[backPc - 1].a == prep.a
            and code[backPc - 1].b == prep.a
            and code[backPc - 1].c == prep.c then
            advStart = backPc - 1
        elseif backPc - 2 >= checkPc + 3
            and code[backPc - 2].op == "ADD"
            and code[backPc - 2].a == prep.a
            and code[backPc - 2].b == prep.a
            and code[backPc - 2].c == prep.c
            and (code[backPc - 1].op == "CLEAR" or code[backPc - 1].op == "CLEARS") then
            advStart = backPc - 2
        elseif backPc - 3 >= checkPc + 3
            and code[backPc - 3].op == "ADD"
            and code[backPc - 3].b == prep.a
            and code[backPc - 3].c == prep.c
            and code[backPc - 2].op == "MOVE"
            and code[backPc - 2].a == prep.a then
            advStart = backPc - 3
        end
        if not advStart then return nil end
        return {
            c1 = prep.a,
            c2 = prep.b,
            c3 = prep.c,
            loopVarReg = iv.a,
            checkPc = checkPc,
            bodyStart = checkPc + 3,
            bodyEnd = advStart - 1,
            advancePc = advStart,
            backPc = backPc,
            endPos = backPc + 1,
        }
    end

    local skipLoopInternalPc = {}
    for pc = 1, #code do
        if code[pc].op == "FORPREP" then
            local nf = matchNumericForHeader(pc)
            if nf then
                for p = nf.checkPc, nf.bodyStart - 1 do skipLoopInternalPc[p] = true end
                for p = nf.advancePc, nf.backPc do skipLoopInternalPc[p] = true end
            end
        elseif loopsByStart[pc] then
            local gf = matchGenericForHeader(pc, loopsByStart[pc])
            if gf then
                for p = pc, gf.bodyStart - 1 do skipLoopInternalPc[p] = true end
            end
        end
    end

    local upwardExposed = {}
    local reassignedLocal = {}
    local curBlockDefs = {}
    local liveHasRead = {}
    local prevBlockId = nil
    for pc = 1, #code do
        local bid = blockIdAt[pc]
        if bid ~= prevBlockId then
            curBlockDefs = {}
            liveHasRead = {}
            prevBlockId = bid
        end
        if not skipLoopInternalPc[pc] then
        local ins = code[pc]
        local op = ins.op
        local function checkRead(r)
            if type(r) == "number" and r > 0 then
                if not curBlockDefs[r] then
                    upwardExposed[r] = true
                else
                    liveHasRead[r] = true
                end
            end
        end
        local function markClear(r)
            if type(r) == "number" and r > 0 then
                curBlockDefs[r] = true
                liveHasRead[r] = nil
            end
        end
        local function markDef(r)
            if type(r) == "number" and r > 0 then
                if liveHasRead[r] then
                    reassignedLocal[r] = true
                end
                curBlockDefs[r] = true
                liveHasRead[r] = nil
            end
        end

        if op == "CLEAR" then
            markClear(ins.a)
        elseif op == "CLEARS" then
            for i = 1, #ins.a do markClear(ins.a[i]) end
        elseif op == "LOAD" or op == "NIL" or op == "GLOBAL" or op == "TABLE" or op == "CLOSURE" or op == "VARARG" then
            markDef(ins.a)
        elseif op == "MOVE" or op == "UNM" or op == "NOT" or op == "LEN" or op == "TAKE"
            or op == "CELL" or op == "GETCELL" then
            checkRead(ins.b)
            markDef(ins.a)
        elseif op == "SETCELL" or op == "SETUP" or op == "SETGLOBAL" then
            checkRead(ins.b)
        elseif op == "GETUP" then
            markDef(ins.a)
        elseif op == "GETTABLE" or BIN_AST_CTOR[op] then
            checkRead(ins.b); checkRead(ins.c)
            markDef(ins.a)
        elseif op == "SETTABLE" then
            checkRead(ins.a); checkRead(ins.b); checkRead(ins.c)
        elseif op == "JTRUE" or op == "JFALSE" or op == "RETURN" or op == "RETURN1" then
            checkRead(ins.a)
        elseif op == "RETURN2" then
            checkRead(ins.a); checkRead(ins.b)
        elseif op == "RETURN3" then
            checkRead(ins.a); checkRead(ins.b); checkRead(ins.c)
        elseif op == "ARGS" then
            for i = 1, #ins.b do checkRead(ins.b[i]) end
            if ins.c ~= 0 then checkRead(ins.c) end
            markDef(ins.a)
        elseif op == "EXPAND" then
            checkRead(ins.a); checkRead(ins.c)
        elseif op == "FORPREP" then
            checkRead(ins.a); checkRead(ins.b); checkRead(ins.c)
            markDef(ins.a); markDef(ins.b); markDef(ins.c)
        elseif op == "FORCHECK" then
            checkRead(ins.b); checkRead(ins.c); checkRead(ins.d)
            markDef(ins.a)
        elseif op == "CALL" then
            checkRead(ins.b); checkRead(ins.c)
            if ins.d ~= 0 then markDef(ins.a) end
        elseif op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3" then
            checkRead(ins.b)
            for i = 1, #ins.c do checkRead(ins.c[i]) end
            if ins.d ~= 0 then markDef(ins.a) end
        elseif op == "TAILCALL" then
            checkRead(ins.a); checkRead(ins.b)
        elseif op == "TAILCALL0" or op == "TAILCALL1" or op == "TAILCALL2" or op == "TAILCALL3" then
            checkRead(ins.a)
            for i = 1, #ins.b do checkRead(ins.b[i]) end
        end
        end
    end

    local isLocalVarReg = {}
    for r, ri in pairs(regInfo) do
        if ri.isParam or ri.isCell or ri.isCapturedByChild or upwardExposed[r] or reassignedLocal[r] then
            isLocalVarReg[r] = true
        end
    end

    local function getRegBinding(r)
        if not regBindings[r] then
            local id = funcScope:addVariable()
            regBindings[r] = { scope = funcScope, id = id, declared = false }
        end
        return regBindings[r]
    end

    local lookupForChildren = {
        funcScope = funcScope,
        captures = captures,
        getRegBinding = function(r)
            return getRegBinding(r, funcScope)
        end,
    }

    local function makeVarExpr(scope, varScope, varId)
        if scope ~= varScope then
            scope:addReferenceToHigherScope(varScope, varId)
        end
        return Ast.VariableExpression(varScope, varId)
    end

    local function makeAssignVar(scope, varScope, varId)
        if scope ~= varScope then
            scope:addReferenceToHigherScope(varScope, varId)
        end
        return Ast.AssignmentVariable(varScope, varId)
    end

    local function countRemainingReadsInRange(reg, fromPc, toPc)
        local cnt = 0
        for p = fromPc, toPc do
            local ins = code[p]
            local op = ins.op
            if op == "MOVE" or op == "CELL" or op == "GETCELL" or op == "UNM" or op == "NOT" or op == "LEN"
                or op == "TAKE" or op == "SETGLOBAL" or op == "SETUP" or op == "SETCELL" then
                if ins.b == reg then cnt = cnt + 1 end
            elseif op == "GETTABLE" or BIN_AST_CTOR[op] then
                if ins.b == reg then cnt = cnt + 1 end
                if ins.c == reg then cnt = cnt + 1 end
            elseif op == "SETTABLE" then
                if ins.a == reg then cnt = cnt + 1 end
                if ins.b == reg then cnt = cnt + 1 end
                if ins.c == reg then cnt = cnt + 1 end
            elseif op == "JTRUE" or op == "JFALSE" or op == "RETURN" or op == "RETURN1" then
                if ins.a == reg then cnt = cnt + 1 end
            elseif op == "RETURN2" then
                if ins.a == reg then cnt = cnt + 1 end
                if ins.b == reg then cnt = cnt + 1 end
            elseif op == "RETURN3" then
                if ins.a == reg then cnt = cnt + 1 end
                if ins.b == reg then cnt = cnt + 1 end
                if ins.c == reg then cnt = cnt + 1 end
            elseif op == "ARGS" then
                for i = 1, #ins.b do if ins.b[i] == reg then cnt = cnt + 1 end end
                if ins.c == reg then cnt = cnt + 1 end
            elseif op == "EXPAND" then
                if ins.a == reg then cnt = cnt + 1 end
                if ins.c == reg then cnt = cnt + 1 end
            elseif op == "FORPREP" then
                if ins.a == reg then cnt = cnt + 1 end
                if ins.b == reg then cnt = cnt + 1 end
                if ins.c == reg then cnt = cnt + 1 end
            elseif op == "FORCHECK" then
                if ins.b == reg then cnt = cnt + 1 end
                if ins.c == reg then cnt = cnt + 1 end
                if ins.d == reg then cnt = cnt + 1 end
            elseif op == "CALL" then
                if ins.b == reg then cnt = cnt + 1 end
                if ins.c == reg then cnt = cnt + 1 end
            elseif op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3" then
                if ins.b == reg then cnt = cnt + 1 end
                for i = 1, #ins.c do if ins.c[i] == reg then cnt = cnt + 1 end end
            elseif op == "TAILCALL" then
                if ins.a == reg then cnt = cnt + 1 end
                if ins.b == reg then cnt = cnt + 1 end
            elseif op == "TAILCALL0" or op == "TAILCALL1" or op == "TAILCALL2" or op == "TAILCALL3" then
                if ins.a == reg then cnt = cnt + 1 end
                for i = 1, #ins.b do if ins.b[i] == reg then cnt = cnt + 1 end end
            end
            if (op == "LOAD" or op == "NIL" or op == "CLEAR" or op == "MOVE" or op == "GLOBAL"
                or op == "CELL" or op == "GETCELL" or op == "GETUP" or op == "TABLE"
                or op == "GETTABLE" or op == "TAKE" or op == "CLOSURE" or op == "VARARG"
                or op == "ARGS" or op == "FORCHECK" or UNARY_AST_CTOR[op] or BIN_AST_CTOR[op]
                or ((op == "CALL" or op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3") and ins.d ~= 0))
                and ins.a == reg then
                break
            elseif op == "CLEARS" then
                local hit = false
                for i = 1, #ins.a do if ins.a[i] == reg then hit = true break end end
                if hit then break end
            end
        end
        return cnt
    end

    local function hasLaterSideEffects(fromPc, toPc)
        for p = fromPc, toPc do
            local op = code[p].op
            if op == "CALL" or op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3"
                or op == "TAILCALL" or op == "TAILCALL0" or op == "TAILCALL1" or op == "TAILCALL2" or op == "TAILCALL3"
                or op == "GETTABLE" or op == "SETTABLE" or BIN_AST_CTOR[op] or UNARY_AST_CTOR[op] then
                return true
            end
        end
        return false
    end

    local decompileRange

    local function matchShortCircuit(jpc, limitPc, pending)
        local ins = code[jpc]
        if ins.op ~= "JFALSE" and ins.op ~= "JTRUE" then return nil end
        local skippedPc = ins.b
        if skippedPc <= jpc + 1 or skippedPc > limitPc + 1 then return nil end
        local jmpIns = code[skippedPc - 1]
        if not jmpIns or jmpIns.op ~= "JMP" then return nil end
        local endPos = jmpIns.a
        if endPos < skippedPc or endPos > limitPc + 1 then return nil end
        for p = skippedPc, endPos - 1 do
            if code[p].op ~= "CLEAR" and code[p].op ~= "CLEARS" then
                return nil
            end
        end
        local prevIns = code[jpc - 1]
        if not prevIns or prevIns.op ~= "MOVE" or prevIns.b ~= ins.a then
            return nil
        end
        local resReg = prevIns.a
        return {
            isAnd = (ins.op == "JFALSE"),
            resReg = resReg,
            leftReg = ins.a,
            rhsStart = jpc + 1,
            rhsEnd = skippedPc - 2,
            endPos = endPos,
        }
    end

    local function isLoopBreakTarget(loopCtx, targetPc)
        if not loopCtx then return false end
        if targetPc == loopCtx.breakTarget then return true end
        if loopCtx.minBreakTarget and loopCtx.maxBreakTarget
            and targetPc >= loopCtx.minBreakTarget and targetPc <= loopCtx.maxBreakTarget then
            return true
        end
        return false
    end

    local function matchIfChain(jpc, limitPc, loopCtx)
        local ins = code[jpc]
        if ins.op ~= "JFALSE" then return nil end
        local nextBranch = ins.b
        if nextBranch <= jpc or nextBranch > limitPc + 1 then return nil end
        if loopCtx and (isLoopBreakTarget(loopCtx, nextBranch) or nextBranch == loopCtx.continueTarget) then
            return nil
        end
        local jmpBeforeNext = code[nextBranch - 1]
        if not jmpBeforeNext or jmpBeforeNext.op ~= "JMP" then return nil end
        local endPos = jmpBeforeNext.a
        if endPos < nextBranch or endPos > limitPc + 1 then return nil end
        if loopCtx and (endPos == loopCtx.continueTarget or endPos < jpc) then
            return nil
        end
        return {
            firstNext = nextBranch,
            endPos = endPos,
        }
    end

    decompileRange = function(startPc, endPc, scope, loopCtx, readHorizonPc)
        local horizonPc = readHorizonPc or endPc
        local stmts = {}
        local pending = {}
        local flushedTemp = {}
        local seq = 0

        local function recordFlushedTemp(r, sc, id)
            if not flushedTemp[r] then flushedTemp[r] = {} end
            flushedTemp[r][#flushedTemp[r] + 1] = { scope = sc, id = id }
        end

        local pc = startPc

        local function hasPendingTableBuild(tblReg, afterPc)
            local limit = math.max(endPc, horizonPc)
            for p = afterPc, limit do
                local ci = code[p]
                if not ci then break end
                local cop = ci.op
                if (cop == "SETTABLE" or cop == "EXPAND") and ci.a == tblReg then
                    return true
                end
                if (cop == "CLEAR" and ci.a == tblReg) then
                    return false
                end
                if cop == "CLEARS" then
                    for j = 1, #ci.a do if ci.a[j] == tblReg then return false end end
                end
                if (cop == "MOVE" and ci.b == tblReg)
                    or (cop == "CELL" and ci.b == tblReg)
                    or (cop == "RETURN1" and ci.a == tblReg)
                    or (cop == "RETURN2" and (ci.a == tblReg or ci.b == tblReg))
                    or (cop == "RETURN3" and (ci.a == tblReg or ci.b == tblReg or ci.c == tblReg))
                    or (cop == "SETGLOBAL" and ci.b == tblReg)
                    or (cop == "SETUP" and ci.b == tblReg)
                    or (cop == "SETCELL" and ci.b == tblReg)
                    or (cop == "GETTABLE" and (ci.b == tblReg or ci.c == tblReg))
                    or (cop == "SETTABLE" and (ci.b == tblReg or ci.c == tblReg)) then
                    return false
                end
                if cop == "ARGS" then
                    for j = 1, #ci.b do if ci.b[j] == tblReg then return false end end
                end
                if cop == "CALL0" or cop == "CALL1" or cop == "CALL2" or cop == "CALL3" then
                    if ci.b == tblReg then return false end
                    for j = 1, #ci.c do if ci.c[j] == tblReg then return false end end
                end
            end
            return false
        end

        local function flushPendingReg(r)
            local p = pending[r]
            if not p or p.kind == "tuple" then return end
            if p.isBuildingTable and hasPendingTableBuild(r, pc + 1) then
                return
            end
            if p.expr.kind == AstKind.NumberExpression
                or p.expr.kind == AstKind.StringExpression
                or p.expr.kind == AstKind.BooleanExpression
                or p.expr.kind == AstKind.NilExpression then
                return
            end
            local tmpId = scope:addVariable()
            stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { tmpId }, { p.expr })
            recordFlushedTemp(r, scope, tmpId)
            if p.deferredNils then
                for dn = 1, #p.deferredNils do
                    stmts[#stmts + 1] = Ast.AssignmentStatement(
                        { makeAssignVar(scope, p.deferredNils[dn].scope, p.deferredNils[dn].id) },
                        { Ast.NilExpression() }
                    )
                end
            end
            pending[r] = {
                kind = "scalar",
                expr = Ast.VariableExpression(scope, tmpId),
                deps = { ["r:" .. tostring(r)] = true },
                impure = false,
                seq = nil,
                readsLeft = p.readsLeft,
            }
        end

        local function flushHazardsBeforeWrite(targetType, targetId)
            local ordered = {}
            for r, p in pairs(pending) do
                if p.kind == "scalar" then
                    local hazard = false
                    if targetType == "reg" and p.deps and p.deps["r:" .. tostring(targetId)] then
                        hazard = true
                    elseif targetType == "up" and (p.impure or (p.deps and p.deps["u:" .. tostring(targetId)])) then
                        hazard = true
                    elseif targetType == "global" and (p.impure or (p.deps and (p.deps["g:" .. tostring(targetId)] or p.deps.anyGlobal))) then
                        hazard = true
                    elseif targetType == "memory" and (p.impure or (p.deps and p.deps.anyTable)) then
                        hazard = true
                    elseif targetType == "allImpure" and p.impure then
                        hazard = true
                    end
                    if hazard then
                        ordered[#ordered + 1] = { r = r, s = p.seq or 0 }
                    end
                end
            end
            table.sort(ordered, function(a, b) return a.s < b.s end)
            for i = 1, #ordered do
                flushPendingReg(ordered[i].r)
            end
        end

        local function flushEarlierImpureExcept(keepRegs)
            local keep = {}
            if keepRegs then
                for i = 1, #keepRegs do keep[keepRegs[i]] = true end
            end
            local minKeepSeq = nil
            if keepRegs then
                local prevSeq = -1
                for i = 1, #keepRegs do
                    local kp = pending[keepRegs[i]]
                    if kp and kp.seq then
                        if kp.seq < prevSeq then
                            minKeepSeq = -1
                            break
                        end
                        prevSeq = kp.seq
                    end
                end
            end
            local ordered = {}
            for r, p in pairs(pending) do
                if p.kind == "scalar" and p.impure then
                    if minKeepSeq == -1 or not keep[r] then
                        ordered[#ordered + 1] = { r = r, s = p.seq or 0 }
                    end
                end
            end
            table.sort(ordered, function(a, b) return a.s < b.s end)
            for i = 1, #ordered do
                if minKeepSeq == -1 or not keep[ordered[i].r] then
                    flushPendingReg(ordered[i].r)
                end
            end
        end

        local function readScalar(r)
            if pending[r] and pending[r].kind == "scalar" then
                local p = pending[r]
                if p.deferredNils and #p.deferredNils > 0 then
                    local tmpId = scope:addVariable()
                    stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { tmpId }, { p.expr })
                    recordFlushedTemp(r, scope, tmpId)
                    for dn = 1, #p.deferredNils do
                        stmts[#stmts + 1] = Ast.AssignmentStatement(
                            { makeAssignVar(scope, p.deferredNils[dn].scope, p.deferredNils[dn].id) },
                            { Ast.NilExpression() }
                        )
                    end
                    p.expr = Ast.VariableExpression(scope, tmpId)
                    p.deps = { ["r:" .. tostring(r)] = true }
                    p.impure = false
                    p.seq = nil
                    p.deferredNils = nil
                end
                if p.readsLeft and p.readsLeft > 1 then
                    p.readsLeft = p.readsLeft - 1
                    return cloneExpr(p.expr), p.deps, p.impure, p.seq
                end
                pending[r] = nil
                return p.expr, p.deps, p.impure, p.seq
            end
            if isLocalVarReg[r] or regBindings[r] then
                local b = getRegBinding(r)
                if not b.declared then
                    if b.scope == scope then
                        stmts[#stmts + 1] = Ast.LocalVariableDeclaration(b.scope, { b.id }, {})
                    else
                        table.insert(b.scope.statements_ref or stmts, 1, Ast.LocalVariableDeclaration(b.scope, { b.id }, {}))
                    end
                    b.declared = true
                end
                local deps = { ["r:" .. tostring(r)] = true }
                return makeVarExpr(scope, b.scope, b.id), deps, false, nil
            end
            return Ast.NilExpression(), {}, false, nil
        end

        local function mergeMeta(list)
            local deps = {}
            local impure = false
            local maxSeq = nil
            for i = 1, #list do
                local item = list[i]
                if item.deps then
                    for k, v in pairs(item.deps) do deps[k] = v end
                end
                if item.impure then impure = true end
                if item.seq and (not maxSeq or item.seq > maxSeq) then
                    maxSeq = item.seq
                end
            end
            return deps, impure, maxSeq
        end

        local function setScalar(dst, expr, deps, impure, pc, endRangePc)
            if impure then
                seq = seq + 1
            end
            local mySeq = impure and seq or nil

            if isLocalVarReg[dst] then
                flushHazardsBeforeWrite("reg", dst)
                local b = getRegBinding(dst, scope)
                if not b.declared and b.scope == scope then
                    stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { b.id }, { expr })
                    b.declared = true
                elseif not b.declared then
                    table.insert(b.scope.statements_ref or stmts, 1, Ast.LocalVariableDeclaration(b.scope, { b.id }, {}))
                    b.declared = true
                    stmts[#stmts + 1] = Ast.AssignmentStatement({ makeAssignVar(scope, b.scope, b.id) }, { expr })
                else
                    stmts[#stmts + 1] = Ast.AssignmentStatement({ makeAssignVar(scope, b.scope, b.id) }, { expr })
                end
                pending[dst] = nil
                return
            end

            local readsLeft = countRemainingReadsInRange(dst, pc + 1, math.max(endRangePc, horizonPc))
            if readsLeft == 0 then
                if impure then
                    local tmpId = scope:addVariable()
                    stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { tmpId }, { expr })
                    recordFlushedTemp(dst, scope, tmpId)
                    expr = Ast.VariableExpression(scope, tmpId)
                    deps = { ["r:" .. tostring(dst)] = true }
                    impure = false
                    mySeq = nil
                end
                pending[dst] = {
                    kind = "scalar",
                    expr = expr,
                    deps = deps or {},
                    impure = impure or false,
                    seq = mySeq,
                    readsLeft = 1,
                }
                return
            end

            if readsLeft > 1 and (impure or expr.kind == AstKind.TableConstructorExpression or expr.kind == AstKind.FunctionLiteralExpression) then
                local nextIns = code[pc + 1]
                local isMethodObj = false
                if readsLeft == 2 and nextIns and nextIns.op == "GETTABLE" and nextIns.b == dst then
                    isMethodObj = true
                end
                if not isMethodObj then
                    local tmpId = scope:addVariable()
                    stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { tmpId }, { expr })
                    recordFlushedTemp(dst, scope, tmpId)
                    pending[dst] = {
                        kind = "scalar",
                        expr = Ast.VariableExpression(scope, tmpId),
                        deps = { ["r:" .. tostring(dst)] = true },
                        impure = false,
                        seq = nil,
                        readsLeft = readsLeft,
                    }
                    return
                end
            end

            pending[dst] = {
                kind = "scalar",
                expr = expr,
                deps = deps or {},
                impure = impure or false,
                seq = mySeq,
                readsLeft = readsLeft,
            }
        end

        while pc <= endPc do
            local ins = code[pc]
            local op = ins.op

            if op == "FORPREP" then
                local nf = matchNumericForHeader(pc)
                if nf and nf.backPc <= endPc then
                    flushEarlierImpureExcept({ nf.c1, nf.c2, nf.c3 })
                    local initExpr = readScalar(nf.c1)
                    local limitExpr = readScalar(nf.c2)
                    local stepExpr = readScalar(nf.c3)

                    local forScope = Scope:new(scope)
                    local varId = forScope:addVariable()
                    local prevBinding = regBindings[nf.loopVarReg]
                    local ivIsCell = (code[nf.checkPc + 2] and code[nf.checkPc + 2].op == "CELL")
                    regBindings[nf.loopVarReg] = { scope = forScope, id = varId, declared = true, isCell = ivIsCell }

                    local subCtx = {
                        breakTarget = nf.endPos,
                        continueTarget = nf.advancePc,
                        usedContinue = false,
                        usedBreak = false,
                    }
                    local bodyStmts = decompileRange(nf.bodyStart, nf.bodyEnd, forScope, subCtx)
                    if subCtx.usedContinue and targetLuaVersion == LuaVersion.Lua51 then
                        bodyStmts = VmDecompiler._wrapLua51Continue(bodyStmts, forScope, subCtx.usedBreak)
                    end
                    regBindings[nf.loopVarReg] = prevBinding

                    local bodyBlock = Ast.Block(bodyStmts, forScope)
                    stmts[#stmts + 1] = Ast.ForStatement(forScope, varId, initExpr, limitExpr, stepExpr, bodyBlock, scope)
                    pc = nf.endPos
                else
                    pc = pc + 1
                end

            elseif loopsByStart[pc] and loopsByStart[pc] <= endPc then
                local backPc = loopsByStart[pc]
                local gf = matchGenericForHeader(pc, backPc)
                if gf then
                    flushEarlierImpureExcept({ gf.iterReg, gf.stateReg, gf.ctrlReg })
                    local e1 = readScalar(gf.iterReg)
                    local e2 = readScalar(gf.stateReg)
                    local e3 = readScalar(gf.ctrlReg)
                    local iterExprs = { e1, e2, e3 }
                    while #iterExprs > 1 and iterExprs[#iterExprs].kind == AstKind.NilExpression do
                        if #iterExprs == 3 and iterExprs[2].kind == AstKind.NilExpression
                            and (e1.kind == AstKind.FunctionCallExpression or e1.kind == AstKind.PassSelfFunctionCallExpression) then
                            iterExprs = { e1 }
                            break
                        end
                        break
                    end

                    local forScope = Scope:new(scope)
                    local ids = {}
                    local savedBindings = {}
                    for i = 1, #gf.loopVarRegs do
                        local r = gf.loopVarRegs[i]
                        savedBindings[r] = regBindings[r]
                        local vid = forScope:addVariable()
                        ids[i] = vid
                        regBindings[r] = { scope = forScope, id = vid, declared = true, isCell = gf.loopVarIsCell[i] }
                    end

                    local subCtx = {
                        breakTarget = gf.endPos,
                        continueTarget = gf.continueTarget,
                        usedContinue = false,
                        usedBreak = false,
                    }
                    local bodyStmts = decompileRange(gf.bodyStart, gf.bodyEnd, forScope, subCtx)
                    if subCtx.usedContinue and targetLuaVersion == LuaVersion.Lua51 then
                        bodyStmts = VmDecompiler._wrapLua51Continue(bodyStmts, forScope, subCtx.usedBreak)
                    end
                    for r, prev in pairs(savedBindings) do regBindings[r] = prev end
                    for i = 1, #gf.loopVarRegs do
                        local r = gf.loopVarRegs[i]
                        if savedBindings[r] == nil then regBindings[r] = nil end
                    end

                    stmts[#stmts + 1] = Ast.ForInStatement(forScope, ids, iterExprs, Ast.Block(bodyStmts, forScope), scope)
                    pc = gf.endPos
                else
                    local whileJfalsePc = nil
                    for p = pc, backPc - 1 do
                        if code[p].op == "JFALSE" and code[p].b == backPc + 1 then
                            whileJfalsePc = p
                            break
                        end
                    end

                    if whileJfalsePc then
                        flushHazardsBeforeWrite("allImpure")
                        local bodyScope = Scope:new(scope)
                        local condPreStmts, condPending = decompileRange(pc, whileJfalsePc - 1, bodyScope, nil, whileJfalsePc)
                        local condReg = code[whileJfalsePc].a
                        local condExpr
                        if condPending and condPending[condReg] and condPending[condReg].kind == "scalar" then
                            condExpr = condPending[condReg].expr
                        else
                            local b = getRegBinding(condReg)
                            condExpr = makeVarExpr((#condPreStmts == 0) and scope or bodyScope, b.scope, b.id)
                        end

                        local subCtx = {
                            breakTarget = backPc + 1,
                            continueTarget = backPc,
                            usedContinue = false,
                            usedBreak = false,
                        }
                        local bodyStmts = decompileRange(whileJfalsePc + 1, backPc - 1, bodyScope, subCtx)
                        if subCtx.usedContinue and targetLuaVersion == LuaVersion.Lua51 then
                            bodyStmts = VmDecompiler._wrapLua51Continue(bodyStmts, bodyScope, subCtx.usedBreak)
                        end

                        if #condPreStmts == 0 then
                            stmts[#stmts + 1] = Ast.WhileStatement(Ast.Block(bodyStmts, bodyScope), condExpr, scope)
                        else
                            local fullBody = {}
                            for i = 1, #condPreStmts do fullBody[#fullBody + 1] = condPreStmts[i] end
                            local brkScope = Scope:new(bodyScope)
                            fullBody[#fullBody + 1] = Ast.IfStatement(
                                Ast.NotExpression(condExpr, false),
                                Ast.Block({ Ast.BreakStatement() }, brkScope),
                                {},
                                nil
                            )
                            for i = 1, #bodyStmts do fullBody[#fullBody + 1] = bodyStmts[i] end
                            stmts[#stmts + 1] = Ast.WhileStatement(Ast.Block(fullBody, bodyScope), Ast.BooleanExpression(true), scope)
                        end
                        pc = backPc + 1
                    else
                        local jtruePc = backPc - 1
                        while jtruePc >= pc and (code[jtruePc].op == "CLEAR" or code[jtruePc].op == "CLEARS") do
                            jtruePc = jtruePc - 1
                        end
                        if jtruePc >= pc and code[jtruePc].op == "JTRUE" and code[jtruePc].b == backPc + 1 then
                            local maxBreak = backPc + 1
                            while maxBreak <= #code and (code[maxBreak].op == "CLEAR" or code[maxBreak].op == "CLEARS") do
                                maxBreak = maxBreak + 1
                            end
                            local repContTarget = nil
                            for p = pc, jtruePc - 1 do
                                if code[p].op == "JMP" and code[p].a > p and code[p].a <= jtruePc then
                                    local enclosedByIf = false
                                    for q = pc, p - 1 do
                                        if (code[q].op == "JFALSE" or code[q].op == "JTRUE") and code[q].b == p + 1 then
                                            enclosedByIf = true
                                            break
                                        end
                                    end
                                    if not enclosedByIf then
                                        repContTarget = code[p].a
                                    end
                                end
                            end

                            flushHazardsBeforeWrite("allImpure")
                            local repScope = Scope:new(scope)
                            local subCtx = {
                                breakTarget = backPc + 1,
                                minBreakTarget = backPc + 1,
                                maxBreakTarget = maxBreak,
                                continueTarget = repContTarget,
                                usedContinue = false,
                                usedBreak = false,
                            }
                            local repStmts, repPending
                            if repContTarget then
                                local bodyPart = decompileRange(pc, repContTarget - 1, repScope, subCtx, jtruePc)
                                local condPart
                                condPart, repPending = decompileRange(repContTarget, jtruePc - 1, repScope, nil, jtruePc)
                                if subCtx.usedContinue and (targetLuaVersion == LuaVersion.Lua51 or #condPart > 0) then
                                    bodyPart = VmDecompiler._wrapLua51Continue(bodyPart, repScope, subCtx.usedBreak)
                                end
                                repStmts = {}
                                for i = 1, #bodyPart do repStmts[#repStmts + 1] = bodyPart[i] end
                                for i = 1, #condPart do repStmts[#repStmts + 1] = condPart[i] end
                            else
                                repStmts, repPending = decompileRange(pc, jtruePc - 1, repScope, subCtx, jtruePc)
                            end
                            local condReg = code[jtruePc].a
                            local condExpr
                            if repPending and repPending[condReg] and repPending[condReg].kind == "scalar" then
                                condExpr = repPending[condReg].expr
                            else
                                local b = getRegBinding(condReg)
                                condExpr = makeVarExpr(repScope, b.scope, b.id)
                            end
                            stmts[#stmts + 1] = Ast.RepeatStatement(condExpr, Ast.Block(repStmts, repScope), scope)
                            pc = backPc + 1
                        else
                            pc = pc + 1
                        end
                    end
                end

            elseif op == "MOVE" and pc < endPc and (code[pc + 1].op == "JFALSE" or code[pc + 1].op == "JTRUE")
                and code[pc + 1].a == ins.b and matchShortCircuit(pc + 1, endPc, pending) then
                local sc = matchShortCircuit(pc + 1, endPc, pending)
                flushEarlierImpureExcept({ sc.leftReg })
                local lhsExpr, lhsDeps, lhsImpure = readScalar(sc.leftReg)
                local rhsScope = Scope:new(scope)
                local rhsStmts, rhsPending = decompileRange(sc.rhsStart, sc.rhsEnd, rhsScope, loopCtx, horizonPc)
                local rhsExpr = nil
                local rhsAlreadyAssigned = false
                local rhsDeps, rhsImpure = {}, false
                if #rhsStmts == 1 and rhsStmts[1].kind == AstKind.AssignmentStatement
                    and #rhsStmts[1].lhs == 1 and rhsStmts[1].lhs[1].kind == AstKind.AssignmentVariable
                    and regBindings[sc.resReg] and rhsStmts[1].lhs[1].id == regBindings[sc.resReg].id then
                    rhsExpr = rhsStmts[1].rhs[1]
                    rhsImpure = true
                    rhsStmts = {}
                elseif rhsPending and rhsPending[sc.resReg] and rhsPending[sc.resReg].kind == "scalar" then
                    rhsExpr = rhsPending[sc.resReg].expr
                    rhsDeps = rhsPending[sc.resReg].deps or {}
                    rhsImpure = rhsPending[sc.resReg].impure or false
                else
                    rhsAlreadyAssigned = true
                end

                if #rhsStmts == 0 and rhsExpr then
                    local ctor = sc.isAnd and Ast.AndExpression or Ast.OrExpression
                    local combined = ctor(lhsExpr, rhsExpr, false)
                    local mDeps = {}
                    for k, v in pairs(lhsDeps or {}) do mDeps[k] = v end
                    for k, v in pairs(rhsDeps or {}) do mDeps[k] = v end
                    setScalar(sc.resReg, combined, mDeps, lhsImpure or rhsImpure, sc.endPos - 1, endPc)
                else
                    local b = getRegBinding(sc.resReg)
                    if not b.declared and b.scope == scope then
                        stmts[#stmts + 1] = Ast.LocalVariableDeclaration(b.scope, { b.id }, { lhsExpr })
                        b.declared = true
                    elseif not b.declared then
                        table.insert(b.scope.statements_ref or stmts, 1, Ast.LocalVariableDeclaration(b.scope, { b.id }, {}))
                        b.declared = true
                        stmts[#stmts + 1] = Ast.AssignmentStatement({ makeAssignVar(scope, b.scope, b.id) }, { lhsExpr })
                    else
                        stmts[#stmts + 1] = Ast.AssignmentStatement({ makeAssignVar(scope, b.scope, b.id) }, { lhsExpr })
                    end
                    local condVar = makeVarExpr(scope, b.scope, b.id)
                    local ifCond = sc.isAnd and condVar or Ast.NotExpression(condVar, false)
                    if not rhsAlreadyAssigned and rhsExpr then
                        rhsStmts[#rhsStmts + 1] = Ast.AssignmentStatement({ makeAssignVar(rhsScope, b.scope, b.id) }, { rhsExpr })
                    end
                    stmts[#stmts + 1] = Ast.IfStatement(ifCond, Ast.Block(rhsStmts, rhsScope), {}, nil)
                    isLocalVarReg[sc.resReg] = true
                end
                pc = sc.endPos

            elseif op == "JFALSE" and matchIfChain(pc, endPc, loopCtx) then
                local ic = matchIfChain(pc, endPc, loopCtx)
                local endPos = ic.endPos
                flushEarlierImpureExcept({ ins.a })
                local firstCond = readScalar(ins.a)
                flushHazardsBeforeWrite("allImpure")

                local arms = {}
                local b1Scope = Scope:new(scope)
                local b1Stmts, b1Pending = decompileRange(pc + 1, ic.firstNext - 2, b1Scope, loopCtx)
                arms[#arms + 1] = { cond = firstCond, stmts = b1Stmts, scope = b1Scope, pending = b1Pending }

                local cur = ic.firstNext
                local elseScope, elseStmts, elsePending

                while cur < endPos do
                    local nextJfalse = nil
                    for p = cur, endPos - 1 do
                        if loopsByStart[p] and loopsByStart[p] < endPos then
                            break
                        end
                        if code[p].op == "JFALSE" and code[p].b <= endPos and code[code[p].b - 1]
                            and code[code[p].b - 1].op == "JMP" and code[code[p].b - 1].a == endPos then
                            nextJfalse = p
                            break
                        end
                    end

                    if nextJfalse then
                        local declSnap = {}
                        for rk, rb in pairs(regBindings) do declSnap[rk] = rb.declared end
                        local hoistedCount = funcScope.statements_ref and #funcScope.statements_ref or 0
                        local childrenCount = #scope.children
                        local cScope = Scope:new(scope)
                        local cPre, cPend = decompileRange(cur, nextJfalse - 1, cScope, loopCtx, nextJfalse)
                        local cReg = code[nextJfalse].a
                        if #cPre == 0 and cPend and cPend[cReg] and cPend[cReg].kind == "scalar" then
                            local eifCond = cPend[cReg].expr
                            local nb = code[nextJfalse].b
                            local armScope = Scope:new(scope)
                            local armStmts, armPend = decompileRange(nextJfalse + 1, nb - 2, armScope, loopCtx, horizonPc)
                            arms[#arms + 1] = { cond = eifCond, stmts = armStmts, scope = armScope, pending = armPend }
                            cur = nb
                        else
                            for rk, rb in pairs(regBindings) do
                                rb.declared = declSnap[rk] or false
                            end
                            if funcScope.statements_ref then
                                while #funcScope.statements_ref > hoistedCount do
                                    table.remove(funcScope.statements_ref)
                                end
                            end
                            while #scope.children > childrenCount do
                                table.remove(scope.children)
                            end
                            elseScope = Scope:new(scope)
                            elseStmts, elsePending = decompileRange(cur, endPos - 1, elseScope, loopCtx, horizonPc)
                            break
                        end
                    else
                        elseScope = Scope:new(scope)
                        elseStmts, elsePending = decompileRange(cur, endPos - 1, elseScope, loopCtx, horizonPc)
                        break
                    end
                end

                local exprResReg = nil
                if elseStmts and #elseStmts == 0 and elsePending then
                    for r, p in pairs(elsePending) do
                        if p.kind == "scalar" and countRemainingReadsInRange(r, endPos, endPc) > 0 then
                            local allHave = true
                            for a = 1, #arms do
                                if #arms[a].stmts ~= 0 or not arms[a].pending or not arms[a].pending[r] then
                                    allHave = false
                                    break
                                end
                            end
                            if allHave then
                                exprResReg = r
                                break
                            end
                        end
                    end
                end

                if exprResReg then
                    if targetLuaVersion == LuaVersion.LuaU then
                        local acc = elsePending[exprResReg].expr
                        for a = #arms, 1, -1 do
                            acc = Ast.IfElseExpression(arms[a].cond, arms[a].pending[exprResReg].expr, {}, acc)
                        end
                        setScalar(exprResReg, acc, {}, true, endPos - 1, endPc)
                    else
                        local tmpId = scope:addVariable()
                        stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { tmpId }, {})
                        local eifs = {}
                        for a = 1, #arms do
                            arms[a].stmts[#arms[a].stmts + 1] = Ast.AssignmentStatement(
                                { makeAssignVar(arms[a].scope, scope, tmpId) },
                                { arms[a].pending[exprResReg].expr }
                            )
                            if a > 1 then
                                eifs[#eifs + 1] = { condition = arms[a].cond, body = Ast.Block(arms[a].stmts, arms[a].scope) }
                            end
                        end
                        elseStmts[#elseStmts + 1] = Ast.AssignmentStatement(
                            { makeAssignVar(elseScope, scope, tmpId) },
                            { elsePending[exprResReg].expr }
                        )
                        stmts[#stmts + 1] = Ast.IfStatement(
                            arms[1].cond,
                            Ast.Block(arms[1].stmts, arms[1].scope),
                            eifs,
                            Ast.Block(elseStmts, elseScope)
                        )
                        setScalar(exprResReg, Ast.VariableExpression(scope, tmpId), {}, false, endPos - 1, endPc)
                    end
                else
                    local eifs = {}
                    for a = 2, #arms do
                        eifs[#eifs + 1] = { condition = arms[a].cond, body = Ast.Block(arms[a].stmts, arms[a].scope) }
                    end
                    local elseBlk = (elseStmts and #elseStmts > 0) and Ast.Block(elseStmts, elseScope) or nil
                    stmts[#stmts + 1] = Ast.IfStatement(arms[1].cond, Ast.Block(arms[1].stmts, arms[1].scope), eifs, elseBlk)
                end

                pc = endPos

            elseif op == "JMP" then
                flushHazardsBeforeWrite("allImpure")
                if isLoopBreakTarget(loopCtx, ins.a) then
                    loopCtx.usedBreak = true
                    stmts[#stmts + 1] = Ast.BreakStatement()
                elseif loopCtx and ins.a == loopCtx.continueTarget then
                    loopCtx.usedContinue = true
                    stmts[#stmts + 1] = Ast.ContinueStatement()
                end
                pc = pc + 1

            elseif op == "LOAD" then
                setScalar(ins.a, makeConstExpr(K[ins.b]), {}, false, pc, endPc)
                pc = pc + 1

            elseif op == "NIL" then
                if pc + 2 <= endPc and isLocalVarReg[ins.a] and scope == funcScope
                    and not (regBindings[ins.a] and regBindings[ins.a].declared)
                    and code[pc + 1].op == "CLOSURE"
                    and code[pc + 2].op == "MOVE" and code[pc + 2].a == ins.a and code[pc + 2].b == code[pc + 1].a then
                    local b = getRegBinding(ins.a)
                    b.declared = true
                    local childLookup = {
                        enclosingScope = scope,
                        captures = captures,
                        getRegBinding = getRegBinding,
                    }
                    local childFn = liftPrototype(proto.children[code[pc + 1].b], childLookup, globalScope, targetLuaVersion, false)
                    stmts[#stmts + 1] = Ast.LocalFunctionDeclaration(b.scope, b.id, childFn.args, childFn.body)
                    pc = pc + 3
                elseif pc + 1 <= endPc and isLocalVarReg[ins.a] and scope == funcScope
                    and not (regBindings[ins.a] and regBindings[ins.a].declared)
                    and code[pc + 1].op == "CLOSURE" and code[pc + 1].a == ins.a then
                    local b = getRegBinding(ins.a)
                    b.declared = true
                    local childLookup = {
                        enclosingScope = scope,
                        captures = captures,
                        getRegBinding = getRegBinding,
                    }
                    local childFn = liftPrototype(proto.children[code[pc + 1].b], childLookup, globalScope, targetLuaVersion, false)
                    stmts[#stmts + 1] = Ast.LocalFunctionDeclaration(b.scope, b.id, childFn.args, childFn.body)
                    pc = pc + 2
                else
                    setScalar(ins.a, Ast.NilExpression(), {}, false, pc, endPc)
                    pc = pc + 1
                end

            elseif op == "CLEAR" or op == "CLEARS" then
                local regs = (op == "CLEAR") and { ins.a } or ins.a
                local laterSideEffects = hasLaterSideEffects(pc + 1, math.max(endPc, horizonPc))
                for i = 1, #regs do
                    local r = regs[i]
                    local oldPend = pending[r]
                    pending[r] = nil
                    if oldPend and (oldPend.isBuildingTable or (oldPend.expr and oldPend.expr.kind == AstKind.TableConstructorExpression)) then
                        local dId = scope:addVariable()
                        stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { dId }, { oldPend.expr })
                        recordFlushedTemp(r, scope, dId)
                    end
                    if laterSideEffects then
                        if (isLocalVarReg[r] and regBindings[r] and regBindings[r].declared and not regBindings[r].isCell)
                            or flushedTemp[r]
                            or (oldPend and oldPend.kind == "unpacked_vars") then
                            flushHazardsBeforeWrite("reg", r)
                        end
                        local holderTup = nil
                        local depKey = "r:" .. tostring(r)
                        for pr, p in pairs(pending) do
                            if (p.kind == "tuple" or (p.isBuildingTable and hasPendingTableBuild(pr, pc + 1)))
                                and p.deps and p.deps[depKey] then
                                holderTup = p
                                break
                            end
                        end
                        local function emitOrDeferNil(varSc, varId)
                            if holderTup then
                                holderTup.deferredNils = holderTup.deferredNils or {}
                                holderTup.deferredNils[#holderTup.deferredNils + 1] = { scope = varSc, id = varId }
                            else
                                stmts[#stmts + 1] = Ast.AssignmentStatement(
                                    { makeAssignVar(scope, varSc, varId) },
                                    { Ast.NilExpression() }
                                )
                            end
                        end
                        if isLocalVarReg[r] and regBindings[r] and regBindings[r].declared and not regBindings[r].isCell then
                            local b = regBindings[r]
                            emitOrDeferNil(b.scope, b.id)
                        end
                        if flushedTemp[r] then
                            for t = 1, #flushedTemp[r] do
                                local ft = flushedTemp[r][t]
                                emitOrDeferNil(ft.scope, ft.id)
                            end
                            flushedTemp[r] = nil
                        end
                        if oldPend and oldPend.kind == "unpacked_vars" then
                            for t = 1, #oldPend.ids do
                                if not (oldPend.taken and oldPend.taken[t]) then
                                    emitOrDeferNil(oldPend.scope, oldPend.ids[t])
                                end
                            end
                        end
                    else
                        flushedTemp[r] = nil
                    end
                    if scope == funcScope and regBindings[r] and regBindings[r].declared
                        and not regBindings[r].isCell and not (regInfo[r] and regInfo[r].isCapturedByChild)
                        and #funcScope.variables < 150 then
                        regBindings[r] = nil
                    end
                end
                pc = pc + 1

            elseif op == "MOVE" then
                local expr, deps, imp = readScalar(ins.b)
                setScalar(ins.a, expr, deps, imp, pc, endPc)
                pc = pc + 1

            elseif op == "GLOBAL" then
                local name = K[ins.b]
                local _, gid = globalScope:resolve(name)
                scope:addReferenceToHigherScope(globalScope, gid)
                setScalar(ins.a, Ast.VariableExpression(globalScope, gid), { ["g:" .. name] = true, anyGlobal = true }, false, pc, endPc)
                pc = pc + 1

            elseif op == "SETGLOBAL" then
                flushEarlierImpureExcept({ ins.b })
                local valExpr = readScalar(ins.b)
                local name = K[ins.a]
                flushHazardsBeforeWrite("global", name)
                local _, gid = globalScope:resolve(name)
                scope:addReferenceToHigherScope(globalScope, gid)
                stmts[#stmts + 1] = Ast.AssignmentStatement({ Ast.AssignmentVariable(globalScope, gid) }, { valExpr })
                pc = pc + 1

            elseif op == "CELL" then
                local initExpr = readScalar(ins.b)
                if initExpr.kind == AstKind.NilExpression and pc + 2 <= endPc
                    and code[pc + 1].op == "CLOSURE"
                    and code[pc + 2].op == "SETCELL" and code[pc + 2].a == ins.a and code[pc + 2].b == code[pc + 1].a then
                    local id = scope:addVariable()
                    regBindings[ins.a] = { scope = scope, id = id, declared = true, isCell = true }
                    local childFn = liftPrototype(proto.children[code[pc + 1].b], lookupForChildren, globalScope, targetLuaVersion, false)
                    stmts[#stmts + 1] = Ast.LocalFunctionDeclaration(scope, id, childFn.args, childFn.body)
                    pc = pc + 3
                else
                    local b = regBindings[ins.a]
                    if not b or b.declared then
                        local id = scope:addVariable()
                        regBindings[ins.a] = { scope = scope, id = id, declared = true, isCell = true }
                        b = regBindings[ins.a]
                    else
                        b.scope = scope
                        b.declared = true
                        b.isCell = true
                    end
                    if initExpr.kind == AstKind.NilExpression then
                        stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { b.id }, {})
                    else
                        stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { b.id }, { initExpr })
                    end
                    pc = pc + 1
                end

            elseif op == "GETCELL" then
                local b = getRegBinding(ins.b, funcScope)
                local expr = makeVarExpr(scope, b.scope, b.id)
                setScalar(ins.a, expr, { ["r:" .. tostring(ins.b)] = true }, false, pc, endPc)
                pc = pc + 1

            elseif op == "SETCELL" then
                flushEarlierImpureExcept({ ins.b })
                local valExpr = readScalar(ins.b)
                flushHazardsBeforeWrite("reg", ins.a)
                local b = getRegBinding(ins.a, funcScope)
                stmts[#stmts + 1] = Ast.AssignmentStatement({ makeAssignVar(scope, b.scope, b.id) }, { valExpr })
                pc = pc + 1

            elseif op == "GETUP" then
                local cap = captures[ins.b]
                local expr = makeVarExpr(scope, cap.scope, cap.id)
                setScalar(ins.a, expr, { ["u:" .. tostring(ins.b)] = true }, false, pc, endPc)
                pc = pc + 1

            elseif op == "SETUP" then
                flushEarlierImpureExcept({ ins.b })
                local valExpr = readScalar(ins.b)
                flushHazardsBeforeWrite("up", ins.a)
                local cap = captures[ins.a]
                stmts[#stmts + 1] = Ast.AssignmentStatement({ makeAssignVar(scope, cap.scope, cap.id) }, { valExpr })
                pc = pc + 1

            elseif op == "CLOSURE" then
                local childLookup = {
                    enclosingScope = scope,
                    captures = captures,
                    getRegBinding = getRegBinding,
                }
                local childFn = liftPrototype(proto.children[ins.b], childLookup, globalScope, targetLuaVersion, false)
                setScalar(ins.a, childFn, {}, false, pc, endPc)
                pc = pc + 1

            elseif op == "TABLE" then
                local entries = {}
                local tblExpr = Ast.TableConstructorExpression(entries)
                pending[ins.a] = {
                    kind = "scalar",
                    expr = tblExpr,
                    isBuildingTable = true,
                    nextArrayIdx = 1,
                    deps = {},
                    impure = false,
                    seq = nil,
                    readsLeft = countRemainingReadsInRange(ins.a, pc + 1, endPc),
                }
                pc = pc + 1

            elseif op == "GETTABLE" then
                flushEarlierImpureExcept({ ins.b, ins.c })
                local baseExpr, d1, i1 = readScalar(ins.b)
                local keyExpr, d2, i2 = readScalar(ins.c)
                local deps = { anyTable = true }
                for k, v in pairs(d1 or {}) do deps[k] = v end
                for k, v in pairs(d2 or {}) do deps[k] = v end
                local idxExpr = Ast.IndexExpression(baseExpr, keyExpr)
                setScalar(ins.a, idxExpr, deps, true, pc, endPc)
                if pending[ins.a] and keyExpr.kind == AstKind.StringExpression and isValidIdent(keyExpr.value) then
                    pending[ins.a].methodCandidate = { objReg = ins.b, baseExpr = baseExpr, methodName = keyExpr.value }
                end
                pc = pc + 1

            elseif op == "SETTABLE" then
                local tblPend = pending[ins.a]
                if tblPend and tblPend.isBuildingTable then
                    flushEarlierImpureExcept({ ins.b, ins.c })
                    local keyExpr, kd, ki = readScalar(ins.b)
                    local valExpr, vd, vi = readScalar(ins.c)
                    for k, v in pairs(kd or {}) do tblPend.deps[k] = v end
                    for k, v in pairs(vd or {}) do tblPend.deps[k] = v end
                    if ki or vi then tblPend.impure = true end
                    if keyExpr.kind == AstKind.NumberExpression and keyExpr.value == tblPend.nextArrayIdx then
                        tblPend.expr.entries[#tblPend.expr.entries + 1] = Ast.TableEntry(valExpr)
                        tblPend.nextArrayIdx = tblPend.nextArrayIdx + 1
                    else
                        tblPend.expr.entries[#tblPend.expr.entries + 1] = Ast.KeyedTableEntry(keyExpr, valExpr)
                    end
                    tblPend.readsLeft = math.max(1, (tblPend.readsLeft or 1) - 1)
                else
                    flushEarlierImpureExcept({ ins.a, ins.b, ins.c })
                    local baseExpr = readScalar(ins.a)
                    local keyExpr = readScalar(ins.b)
                    local valExpr = readScalar(ins.c)
                    flushHazardsBeforeWrite("memory")
                    stmts[#stmts + 1] = Ast.AssignmentStatement(
                        { Ast.AssignmentIndexing(baseExpr, keyExpr) },
                        { valExpr }
                    )
                end
                pc = pc + 1

            elseif op == "EXPAND" then
                local tblPend = pending[ins.a]
                local tup = pending[ins.c]
                pending[ins.c] = nil
                local list = (tup and tup.exprList) or {}
                if tblPend and tblPend.isBuildingTable and ins.b == tblPend.nextArrayIdx then
                    for k, v in pairs((tup and tup.deps) or {}) do tblPend.deps[k] = v end
                    if tup and tup.impure then tblPend.impure = true end
                    if tup and tup.deferredNils then
                        tblPend.deferredNils = tblPend.deferredNils or {}
                        for dn = 1, #tup.deferredNils do
                            tblPend.deferredNils[#tblPend.deferredNils + 1] = tup.deferredNils[dn]
                        end
                    end
                    for i = 1, #list do
                        tblPend.expr.entries[#tblPend.expr.entries + 1] = Ast.TableEntry(list[i])
                    end
                    tblPend.nextArrayIdx = tblPend.nextArrayIdx + #list
                    tblPend.readsLeft = math.max(1, (tblPend.readsLeft or 1) - 1)
                else
                    local baseExpr = readScalar(ins.a)
                    for i = 1, #list do
                        stmts[#stmts + 1] = Ast.AssignmentStatement(
                            { Ast.AssignmentIndexing(cloneExpr(baseExpr), Ast.NumberExpression(ins.b + i - 1)) },
                            { list[i] }
                        )
                    end
                end
                pc = pc + 1

            elseif UNARY_AST_CTOR[op] then
                flushEarlierImpureExcept({ ins.b })
                local subExpr, d1 = readScalar(ins.b)
                local impure = (op ~= "NOT")
                setScalar(ins.a, UNARY_AST_CTOR[op](subExpr, false), d1, impure, pc, endPc)
                pc = pc + 1

            elseif BIN_AST_CTOR[op] then
                flushEarlierImpureExcept({ ins.b, ins.c })
                local lExpr, d1 = readScalar(ins.b)
                local rExpr, d2 = readScalar(ins.c)
                local deps = {}
                for k, v in pairs(d1 or {}) do deps[k] = v end
                for k, v in pairs(d2 or {}) do deps[k] = v end
                setScalar(ins.a, BIN_AST_CTOR[op](lExpr, rExpr, false), deps, true, pc, endPc)
                pc = pc + 1

            elseif op == "VARARG" then
                local maxTake = 0
                local onlyTakes = true
                for p = pc + 1, endPc do
                    local ci = code[p]
                    if ci.op == "TAKE" and ci.b == ins.a then
                        if ci.c > maxTake then maxTake = ci.c end
                    elseif (ci.op == "CLEAR" and ci.a == ins.a) then
                        break
                    elseif ci.op == "CLEARS" then
                        local hit = false
                        for j = 1, #ci.a do if ci.a[j] == ins.a then hit = true break end end
                        if hit then break end
                    elseif (ci.op == "ARGS" and ci.c == ins.a) or (ci.op == "RETURN" and ci.a == ins.a)
                        or (ci.op == "EXPAND" and ci.c == ins.a) then
                        onlyTakes = false
                        break
                    end
                end
                if onlyTakes and maxTake == 1 then
                    local vexpr = Ast.VarargExpression()
                    vexpr.isParenthesizedExpression = true
                    pending[ins.a] = { kind = "single_tuple", expr = vexpr }
                elseif onlyTakes and maxTake > 1 then
                    local ids = {}
                    for i = 1, maxTake do ids[i] = scope:addVariable() end
                    stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, ids, { Ast.VarargExpression() })
                    pending[ins.a] = { kind = "unpacked_vars", scope = scope, ids = ids }
                else
                    pending[ins.a] = { kind = "tuple", exprList = { Ast.VarargExpression() }, hasExpandTail = true }
                end
                pc = pc + 1

            elseif op == "TAKE" then
                local src = pending[ins.b]
                if src and src.kind == "single_tuple" and ins.c == 1 then
                    pending[ins.b] = nil
                    setScalar(ins.a, src.expr, {}, false, pc, endPc)
                elseif src and src.kind == "unpacked_vars" then
                    local id = src.ids[ins.c]
                    if id then
                        src.taken = src.taken or {}
                        src.taken[ins.c] = true
                        recordFlushedTemp(ins.a, src.scope, id)
                    end
                    local e = id and Ast.VariableExpression(src.scope, id) or Ast.NilExpression()
                    setScalar(ins.a, e, { ["r:" .. tostring(ins.a)] = true }, false, pc, endPc)
                else
                    setScalar(ins.a, Ast.NilExpression(), {}, false, pc, endPc)
                end
                pc = pc + 1

            elseif op == "ARGS" then
                local keep = {}
                for i = 1, #ins.b do keep[#keep + 1] = ins.b[i] end
                if ins.c ~= 0 then keep[#keep + 1] = ins.c end
                flushEarlierImpureExcept(keep)

                local list = {}
                local deps = {}
                local imp = false
                for i = 1, #ins.b do
                    local e, d, im = readScalar(ins.b[i])
                    list[#list + 1] = e
                    for k, v in pairs(d or {}) do deps[k] = v end
                    if im then imp = true end
                end
                local hasTail = false
                local defNils = nil
                if ins.c ~= 0 then
                    local tail = pending[ins.c]
                    pending[ins.c] = nil
                    if tail and tail.exprList then
                        for k, v in pairs(tail.deps or {}) do deps[k] = v end
                        if tail.impure then imp = true end
                        defNils = tail.deferredNils
                        for i = 1, #tail.exprList do
                            list[#list + 1] = tail.exprList[i]
                        end
                        hasTail = true
                    end
                elseif #list > 0 and isExpandableExpr(list[#list]) then
                    list[#list].isParenthesizedExpression = true
                end
                pending[ins.a] = { kind = "tuple", exprList = list, hasExpandTail = hasTail, deps = deps, impure = imp, deferredNils = defNils }
                pc = pc + 1

            elseif op == "CALL" or op == "CALL0" or op == "CALL1" or op == "CALL2" or op == "CALL3" then
                local fnPend = pending[ins.b]
                local methodCand = fnPend and fnPend.methodCandidate or nil
                local argList = {}
                local callDeps = { anyTable = true, anyGlobal = true }

                if op == "CALL" then
                    flushEarlierImpureExcept({ ins.b, ins.c })
                    local fnExpr, fd = readScalar(ins.b)
                    for k, v in pairs(fd or {}) do callDeps[k] = v end
                    local tup = pending[ins.c]
                    pending[ins.c] = nil
                    if tup and tup.deps then
                        for k, v in pairs(tup.deps) do callDeps[k] = v end
                    end
                    local tupDefNils = tup and tup.deferredNils or nil
                    argList = (tup and tup.exprList) or {}
                    local callExpr
                    if methodCand and #argList >= 1 then
                        local selfExpr = argList[1]
                        if (selfExpr.kind == AstKind.VariableExpression and methodCand.baseExpr.kind == AstKind.VariableExpression
                            and selfExpr.scope == methodCand.baseExpr.scope and selfExpr.id == methodCand.baseExpr.id) then
                            table.remove(argList, 1)
                            callExpr = Ast.PassSelfFunctionCallExpression(methodCand.baseExpr, methodCand.methodName, argList)
                        else
                            callExpr = Ast.FunctionCallExpression(fnExpr, argList)
                        end
                    else
                        callExpr = Ast.FunctionCallExpression(fnExpr, argList)
                    end

                    flushHazardsBeforeWrite("allImpure")
                    if ins.d == 0 then
                        if callExpr.kind == AstKind.PassSelfFunctionCallExpression then
                            stmts[#stmts + 1] = Ast.PassSelfFunctionCallStatement(callExpr.base, callExpr.passSelfFunctionName, callExpr.args)
                        else
                            stmts[#stmts + 1] = Ast.FunctionCallStatement(callExpr.base, callExpr.args)
                        end
                        if tupDefNils then
                            for dn = 1, #tupDefNils do
                                stmts[#stmts + 1] = Ast.AssignmentStatement(
                                    { makeAssignVar(scope, tupDefNils[dn].scope, tupDefNils[dn].id) },
                                    { Ast.NilExpression() }
                                )
                            end
                        end
                    elseif ins.d == 1 then
                        if tupDefNils then
                            local tmpId = scope:addVariable()
                            stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, { tmpId }, { callExpr })
                            recordFlushedTemp(ins.a, scope, tmpId)
                            for dn = 1, #tupDefNils do
                                stmts[#stmts + 1] = Ast.AssignmentStatement(
                                    { makeAssignVar(scope, tupDefNils[dn].scope, tupDefNils[dn].id) },
                                    { Ast.NilExpression() }
                                )
                            end
                            setScalar(ins.a, Ast.VariableExpression(scope, tmpId), { ["r:" .. tostring(ins.a)] = true }, false, pc, endPc)
                        else
                            setScalar(ins.a, callExpr, callDeps, true, pc, endPc)
                        end
                    else
                        VmDecompiler._storeMultiCallResult(ins.a, callExpr, pc, endPc, code, pending, scope, stmts, callDeps, tupDefNils, makeAssignVar)
                    end
                else
                    local keep = { ins.b }
                    for i = 1, #ins.c do keep[#keep + 1] = ins.c[i] end
                    flushEarlierImpureExcept(keep)
                    local fnExpr, fd = readScalar(ins.b)
                    for k, v in pairs(fd or {}) do callDeps[k] = v end
                    for i = 1, #ins.c do
                        local ae, ad = readScalar(ins.c[i])
                        argList[i] = ae
                        for k, v in pairs(ad or {}) do callDeps[k] = v end
                    end
                    if #argList > 0 and isExpandableExpr(argList[#argList]) then
                        argList[#argList].isParenthesizedExpression = true
                    end
                    local callExpr
                    if methodCand and #argList >= 1
                        and argList[1].kind == AstKind.VariableExpression
                        and methodCand.baseExpr.kind == AstKind.VariableExpression
                        and argList[1].scope == methodCand.baseExpr.scope
                        and argList[1].id == methodCand.baseExpr.id then
                        table.remove(argList, 1)
                        callExpr = Ast.PassSelfFunctionCallExpression(methodCand.baseExpr, methodCand.methodName, argList)
                    else
                        callExpr = Ast.FunctionCallExpression(fnExpr, argList)
                    end

                    flushHazardsBeforeWrite("allImpure")
                    if ins.d == 0 then
                        if callExpr.kind == AstKind.PassSelfFunctionCallExpression then
                            stmts[#stmts + 1] = Ast.PassSelfFunctionCallStatement(callExpr.base, callExpr.passSelfFunctionName, callExpr.args)
                        else
                            stmts[#stmts + 1] = Ast.FunctionCallStatement(callExpr.base, callExpr.args)
                        end
                    elseif ins.d == 1 then
                        setScalar(ins.a, callExpr, callDeps, true, pc, endPc)
                    else
                        VmDecompiler._storeMultiCallResult(ins.a, callExpr, pc, endPc, code, pending, scope, stmts, callDeps, nil, makeAssignVar)
                    end
                end
                pc = pc + 1

            elseif op == "TAILCALL" or op == "TAILCALL0" or op == "TAILCALL1" or op == "TAILCALL2" or op == "TAILCALL3" then
                local fnPend = pending[ins.a]
                local methodCand = fnPend and fnPend.methodCandidate or nil
                local argList = {}
                local callExpr
                if op == "TAILCALL" then
                    flushEarlierImpureExcept({ ins.a, ins.b })
                    local fnExpr = readScalar(ins.a)
                    local tup = pending[ins.b]
                    pending[ins.b] = nil
                    argList = (tup and tup.exprList) or {}
                    if methodCand and #argList >= 1 and argList[1].kind == AstKind.VariableExpression
                        and methodCand.baseExpr.kind == AstKind.VariableExpression
                        and argList[1].scope == methodCand.baseExpr.scope and argList[1].id == methodCand.baseExpr.id then
                        table.remove(argList, 1)
                        callExpr = Ast.PassSelfFunctionCallExpression(methodCand.baseExpr, methodCand.methodName, argList)
                    else
                        callExpr = Ast.FunctionCallExpression(fnExpr, argList)
                    end
                else
                    local keep = { ins.a }
                    for i = 1, #ins.b do keep[#keep + 1] = ins.b[i] end
                    flushEarlierImpureExcept(keep)
                    local fnExpr = readScalar(ins.a)
                    for i = 1, #ins.b do argList[i] = readScalar(ins.b[i]) end
                    if #argList > 0 and isExpandableExpr(argList[#argList]) then
                        argList[#argList].isParenthesizedExpression = true
                    end
                    if methodCand and #argList >= 1
                        and argList[1].kind == AstKind.VariableExpression
                        and methodCand.baseExpr.kind == AstKind.VariableExpression
                        and argList[1].scope == methodCand.baseExpr.scope
                        and argList[1].id == methodCand.baseExpr.id then
                        table.remove(argList, 1)
                        callExpr = Ast.PassSelfFunctionCallExpression(methodCand.baseExpr, methodCand.methodName, argList)
                    else
                        callExpr = Ast.FunctionCallExpression(fnExpr, argList)
                    end
                end
                flushHazardsBeforeWrite("allImpure")
                stmts[#stmts + 1] = Ast.ReturnStatement({ callExpr })
                pc = pc + 1

            elseif op == "RETURN0" then
                flushHazardsBeforeWrite("allImpure")
                if not (pc == #code and (isRootChunk or (#stmts > 0 and stmts[#stmts].kind == AstKind.ReturnStatement) or #stmts >= 0)) then
                    stmts[#stmts + 1] = Ast.ReturnStatement({})
                end
                pc = pc + 1

            elseif op == "RETURN1" or op == "RETURN2" or op == "RETURN3" then
                local regs = { ins.a }
                if op == "RETURN2" or op == "RETURN3" then regs[#regs + 1] = ins.b end
                if op == "RETURN3" then regs[#regs + 1] = ins.c end
                flushEarlierImpureExcept(regs)
                local args = {}
                for i = 1, #regs do
                    args[i] = readScalar(regs[i])
                end
                if isExpandableExpr(args[#args]) then
                    args[#args].isParenthesizedExpression = true
                end
                flushHazardsBeforeWrite("allImpure")
                stmts[#stmts + 1] = Ast.ReturnStatement(args)
                pc = pc + 1

            elseif op == "RETURN" then
                local tup = pending[ins.a]
                pending[ins.a] = nil
                local args = (tup and tup.exprList) or {}
                flushHazardsBeforeWrite("allImpure")
                stmts[#stmts + 1] = Ast.ReturnStatement(args)
                pc = pc + 1

            else
                pc = pc + 1
            end
        end

        return stmts, pending
    end

    funcScope.statements_ref = {}
    local bodyStmts = decompileRange(1, #code, funcScope, nil)
    if #funcScope.statements_ref > 0 then
        for i = #funcScope.statements_ref, 1, -1 do
            table.insert(bodyStmts, 1, funcScope.statements_ref[i])
        end
    end
    funcScope.statements_ref = nil

    if #bodyStmts > 0 and bodyStmts[#bodyStmts].kind == AstKind.ReturnStatement and #bodyStmts[#bodyStmts].args == 0 then
        table.remove(bodyStmts, #bodyStmts)
    end

    local bodyBlock = Ast.Block(bodyStmts, funcScope)
    if isRootChunk then
        return bodyBlock
    end
    return Ast.FunctionLiteralExpression(paramArgs, bodyBlock)
end

function VmDecompiler._storeMultiCallResult(dstReg, callExpr, pc, endPc, code, pending, scope, stmts, callDeps, deferredNils, makeAssignVar)
    local maxTake = 0
    local onlyTakes = true
    for p = pc + 1, endPc do
        local ci = code[p]
        if ci.op == "TAKE" and ci.b == dstReg then
            if ci.c > maxTake then maxTake = ci.c end
        elseif ci.op == "CLEAR" and ci.a == dstReg then
            break
        elseif ci.op == "CLEARS" then
            local hit = false
            for j = 1, #ci.a do if ci.a[j] == dstReg then hit = true break end end
            if hit then break end
        elseif (ci.op == "ARGS" and ci.c == dstReg) or (ci.op == "RETURN" and ci.a == dstReg)
            or (ci.op == "EXPAND" and ci.c == dstReg) then
            onlyTakes = false
            break
        end
    end
    if onlyTakes and maxTake > 0 then
        local ids = {}
        for i = 1, maxTake do ids[i] = scope:addVariable() end
        stmts[#stmts + 1] = Ast.LocalVariableDeclaration(scope, ids, { callExpr })
        if deferredNils and makeAssignVar then
            for dn = 1, #deferredNils do
                stmts[#stmts + 1] = Ast.AssignmentStatement(
                    { makeAssignVar(scope, deferredNils[dn].scope, deferredNils[dn].id) },
                    { Ast.NilExpression() }
                )
            end
        end
        pending[dstReg] = { kind = "unpacked_vars", scope = scope, ids = ids }
    else
        pending[dstReg] = { kind = "tuple", exprList = { callExpr }, hasExpandTail = true, deps = callDeps or {}, impure = true, deferredNils = deferredNils }
    end
end

function VmDecompiler._wrapLua51Continue(bodyStmts, parentScope, hasOuterBreak)
    local brkId = hasOuterBreak and parentScope:addVariable() or nil
    local repScope = Scope:new(parentScope)

    local function rewrite(stmtList, curScope)
        for i = 1, #stmtList do
            local s = stmtList[i]
            if s.kind == AstKind.ContinueStatement then
                local dScope = Scope:new(curScope)
                stmtList[i] = Ast.DoStatement(Ast.Block({ Ast.BreakStatement() }, dScope))
            elseif s.kind == AstKind.BreakStatement and brkId then
                local dScope = Scope:new(curScope)
                curScope:addReferenceToHigherScope(parentScope, brkId)
                stmtList[i] = Ast.DoStatement(Ast.Block({
                    Ast.AssignmentStatement({ Ast.AssignmentVariable(parentScope, brkId) }, { Ast.BooleanExpression(true) }),
                    Ast.BreakStatement(),
                }, dScope))
            elseif s.kind == AstKind.IfStatement then
                rewrite(s.body.statements, s.body.scope)
                for j = 1, #s.elseifs do
                    rewrite(s.elseifs[j].body.statements, s.elseifs[j].body.scope)
                end
                if s.elsebody then
                    rewrite(s.elsebody.statements, s.elsebody.scope)
                end
            elseif s.kind == AstKind.DoStatement then
                rewrite(s.body.statements, s.body.scope)
            end
        end
    end

    rewrite(bodyStmts, repScope)
    local out = {}
    if brkId then
        out[#out + 1] = Ast.LocalVariableDeclaration(parentScope, { brkId }, { Ast.BooleanExpression(false) })
    end
    out[#out + 1] = Ast.RepeatStatement(Ast.BooleanExpression(true), Ast.Block(bodyStmts, repScope), parentScope)
    if brkId then
        local ifSc = Scope:new(parentScope)
        out[#out + 1] = Ast.IfStatement(
            Ast.VariableExpression(parentScope, brkId),
            Ast.Block({ Ast.BreakStatement() }, ifSc),
            {},
            nil
        )
    end
    return out
end

local function isDeadCffSetupStmt(stmt)
    if stmt.kind == AstKind.LocalFunctionDeclaration then
        return true
    elseif stmt.kind == AstKind.LocalVariableDeclaration then
        if not stmt.expressions then return true end
        for _, ex in ipairs(stmt.expressions) do
            if ex.kind ~= AstKind.NilExpression
                and ex.kind ~= AstKind.VariableExpression
                and ex.kind ~= AstKind.OrExpression
                and ex.kind ~= AstKind.IndexExpression
                and ex.kind ~= AstKind.TableConstructorExpression then
                return false
            end
        end
        return true
    elseif stmt.kind == AstKind.AssignmentStatement then
        for _, r in ipairs(stmt.rhs) do
            if r.kind ~= AstKind.NilExpression
                and r.kind ~= AstKind.StringExpression
                and r.kind ~= AstKind.NumberExpression
                and r.kind ~= AstKind.BooleanExpression
                and r.kind ~= AstKind.IndexExpression
                and r.kind ~= AstKind.TableConstructorExpression
                and r.kind ~= AstKind.VariableExpression then
                return false
            end
        end
        return true
    end
    return false
end

function VmDecompiler.decompile(ast, targetLuaVersion)
    targetLuaVersion = targetLuaVersion or LuaVersion.Lua51
    local stmts = ast.body and ast.body.statements
    if not stmts or #stmts == 0 then return false end

    local retStmt = stmts[#stmts]
    if retStmt.kind ~= AstKind.ReturnStatement or #retStmt.args ~= 1 then return false end

    local call = retStmt.args[1]
    local dataTbl = nil
    local vmSpanStart = #stmts

    if call.kind == AstKind.FunctionCallExpression
        and not call.isParenthesizedExpression
        and call.base.kind == AstKind.FunctionLiteralExpression
        and #call.args == 2
        and call.args[2].kind == AstKind.VarargExpression then
        dataTbl = call.args[1]
    elseif call.kind == AstKind.FunctionCallExpression
        and call.base.kind == AstKind.VariableExpression
        and #call.args == 1
        and call.args[1].kind == AstKind.VariableExpression then
        local curSc, curId = call.args[1].scope, call.args[1].id
        local foundVmCall = nil
        local callStmtIdx = nil
        for k = #stmts - 1, math.max(1, #stmts - 10), -1 do
            local sk = stmts[k]
            if sk.kind == AstKind.AssignmentStatement and #sk.lhs == 1 and #sk.rhs == 1
                and sk.lhs[1].kind == AstKind.AssignmentVariable
                and sk.lhs[1].scope == curSc and sk.lhs[1].id == curId then
                local r = sk.rhs[1]
                if r.kind == AstKind.VariableExpression then
                    curSc, curId = r.scope, r.id
                elseif r.kind == AstKind.FunctionCallExpression and #r.args == 1
                    and r.args[1].kind == AstKind.FunctionCallExpression then
                    local innerCall = r.args[1]
                    if innerCall.base.kind == AstKind.FunctionLiteralExpression
                        and #innerCall.args == 2
                        and innerCall.args[2].kind == AstKind.VarargExpression then
                        foundVmCall = innerCall
                        callStmtIdx = k
                        break
                    end
                elseif r.kind == AstKind.FunctionCallExpression
                    and r.base.kind == AstKind.FunctionLiteralExpression
                    and #r.args == 2
                    and r.args[2].kind == AstKind.VarargExpression then
                    foundVmCall = r
                    callStmtIdx = k
                    break
                end
            end
        end
        if foundVmCall and callStmtIdx then
            call = foundVmCall
            vmSpanStart = callStmtIdx
            if foundVmCall.args[1].kind == AstKind.TableConstructorExpression then
                dataTbl = foundVmCall.args[1]
            elseif foundVmCall.args[1].kind == AstKind.VariableExpression then
                local pSc, pId = foundVmCall.args[1].scope, foundVmCall.args[1].id
                for k = callStmtIdx - 1, math.max(1, callStmtIdx - 10), -1 do
                    local sk = stmts[k]
                    if sk.kind == AstKind.AssignmentStatement and #sk.lhs == 1 and #sk.rhs == 1
                        and sk.lhs[1].kind == AstKind.AssignmentVariable
                        and sk.lhs[1].scope == pSc and sk.lhs[1].id == pId
                        and sk.rhs[1].kind == AstKind.TableConstructorExpression then
                        dataTbl = sk.rhs[1]
                        vmSpanStart = k
                        break
                    end
                end
            end
        end
    end

    if not dataTbl or dataTbl.kind ~= AstKind.TableConstructorExpression or #dataTbl.entries ~= 1 then return false end
    if dataTbl.entries[1].kind ~= AstKind.TableEntry then return false end

    local rootProto = parsePrototypeTable(dataTbl.entries[1].value)
    if not rootProto then return false end

    local layout = extractLayout(call.base, ast.globalScope)
    if not layout then return false end

    decodePrototypes(rootProto, layout)
    local liftedBlock = liftPrototype(rootProto, nil, ast.globalScope, targetLuaVersion, true)

    local allPriorDead = true
    for k = 1, vmSpanStart - 1 do
        if not isDeadCffSetupStmt(stmts[k]) then
            allPriorDead = false
            break
        end
    end

    if vmSpanStart == 1 or allPriorDead then
        liftedBlock.scope:setParent(ast.globalScope)
        ast.body = liftedBlock
    else
        for k = #stmts, vmSpanStart + 1, -1 do
            table.remove(stmts, k)
        end
        liftedBlock.scope:setParent(ast.body.scope)
        stmts[vmSpanStart] = Ast.DoStatement(liftedBlock)
    end
    return true
end

return VmDecompiler

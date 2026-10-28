local Ast = require("prometheus.ast")
local Scope = require("prometheus.scope")
local Enums = require("prometheus.enums")
local visitast = require("prometheus.visitast")

local AstKind = Ast.AstKind
local LuaVersion = Enums.LuaVersion
local unpack = unpack or table.unpack

local CffDecompiler = {}

local COMPOUND_CONSTRUCTORS = {
    [AstKind.CompoundAddStatement] = Ast.CompoundAddStatement,
    [AstKind.CompoundSubStatement] = Ast.CompoundSubStatement,
    [AstKind.CompoundMulStatement] = Ast.CompoundMulStatement,
    [AstKind.CompoundDivStatement] = Ast.CompoundDivStatement,
    [AstKind.CompoundModStatement] = Ast.CompoundModStatement,
    [AstKind.CompoundPowStatement] = Ast.CompoundPowStatement,
    [AstKind.CompoundConcatStatement] = Ast.CompoundConcatStatement,
}

local BIN_CONSTRUCTORS = {
    [AstKind.AddExpression] = Ast.AddExpression,
    [AstKind.SubExpression] = Ast.SubExpression,
    [AstKind.MulExpression] = Ast.MulExpression,
    [AstKind.DivExpression] = Ast.DivExpression,
    [AstKind.ModExpression] = Ast.ModExpression,
    [AstKind.PowExpression] = Ast.PowExpression,
    [AstKind.StrCatExpression] = Ast.StrCatExpression,
    [AstKind.LessThanExpression] = Ast.LessThanExpression,
    [AstKind.GreaterThanExpression] = Ast.GreaterThanExpression,
    [AstKind.LessThanOrEqualsExpression] = Ast.LessThanOrEqualsExpression,
    [AstKind.GreaterThanOrEqualsExpression] = Ast.GreaterThanOrEqualsExpression,
    [AstKind.EqualsExpression] = Ast.EqualsExpression,
    [AstKind.NotEqualsExpression] = Ast.NotEqualsExpression,
    [AstKind.AndExpression] = Ast.AndExpression,
    [AstKind.OrExpression] = Ast.OrExpression,
}

local UNARY_CONSTRUCTORS = {
    [AstKind.NotExpression] = Ast.NotExpression,
    [AstKind.NegateExpression] = Ast.NegateExpression,
    [AstKind.LenExpression] = Ast.LenExpression,
}

local function isVarRef(node, scope, id)
    if not node or (node.kind ~= AstKind.VariableExpression and node.kind ~= AstKind.AssignmentVariable)
        or node.scope ~= scope then
        return false
    end
    if type(id) == "table" then
        return id[node.id] == true
    end
    return node.id == id
end

local function visitSub(rootNode, previsit, postvisit, globalScope)
    if not rootNode then return end
    if rootNode.kind == AstKind.TopNode then
        visitast(rootNode, previsit, postvisit)
        return
    end
    local dummyScope = Scope:new(globalScope or Scope:newGlobal())
    local block
    if rootNode.kind == AstKind.Block then
        block = rootNode
    elseif rootNode.isConstant ~= nil or BIN_CONSTRUCTORS[rootNode.kind] or UNARY_CONSTRUCTORS[rootNode.kind]
        or rootNode.kind == AstKind.FunctionCallExpression or rootNode.kind == AstKind.PassSelfFunctionCallExpression
        or rootNode.kind == AstKind.IndexExpression or rootNode.kind == AstKind.TableConstructorExpression
        or rootNode.kind == AstKind.FunctionLiteralExpression or rootNode.kind == AstKind.VarargExpression
        or rootNode.kind == AstKind.VariableExpression or rootNode.kind == AstKind.IfElseExpression then
        block = Ast.Block({ Ast.ReturnStatement({ rootNode }) }, dummyScope)
    else
        block = Ast.Block({ rootNode }, dummyScope)
    end
    visitast(Ast.TopNode(block, globalScope or dummyScope.parentScope), previsit, postvisit)
end

local function negateExpr(expr)
    if expr.kind == AstKind.NotExpression then
        return expr.rhs
    elseif expr.kind == AstKind.EqualsExpression then
        return Ast.NotEqualsExpression(expr.lhs, expr.rhs)
    elseif expr.kind == AstKind.NotEqualsExpression then
        return Ast.EqualsExpression(expr.lhs, expr.rhs)
    end
    return Ast.NotExpression(expr)
end

local function wrapContinueForLua51(bodyStmts, loopScope, hasOuterBreak)
    local contScope = Scope:new(loopScope)
    local brkFlagId = nil
    if hasOuterBreak then
        brkFlagId = loopScope:addVariable()
    end

    local function rewriteInStmt(stmt, curScope)
        if not stmt then return stmt end
        local k = stmt.kind
        if k == AstKind.WhileStatement or k == AstKind.RepeatStatement
            or k == AstKind.ForStatement or k == AstKind.ForInStatement
            or k == AstKind.FunctionDeclaration or k == AstKind.LocalFunctionDeclaration then
            return stmt
        end
        if k == AstKind.ContinueStatement then
            return Ast.BreakStatement()
        end
        if k == AstKind.BreakStatement and brkFlagId then
            curScope:addReferenceToHigherScope(loopScope, brkFlagId)
            return Ast.DoStatement(Ast.Block({
                Ast.AssignmentStatement({ Ast.AssignmentVariable(loopScope, brkFlagId) }, { Ast.BooleanExpression(true) }),
                Ast.BreakStatement(),
            }, Scope:new(curScope)))
        end
        if k == AstKind.IfStatement then
            for i = 1, #stmt.body.statements do
                stmt.body.statements[i] = rewriteInStmt(stmt.body.statements[i], stmt.body.scope)
            end
            for _, eif in ipairs(stmt.elseifs) do
                for i = 1, #eif.body.statements do
                    eif.body.statements[i] = rewriteInStmt(eif.body.statements[i], eif.body.scope)
                end
            end
            if stmt.elsebody then
                for i = 1, #stmt.elsebody.statements do
                    stmt.elsebody.statements[i] = rewriteInStmt(stmt.elsebody.statements[i], stmt.elsebody.scope)
                end
            end
        elseif k == AstKind.DoStatement then
            for i = 1, #stmt.body.statements do
                stmt.body.statements[i] = rewriteInStmt(stmt.body.statements[i], stmt.body.scope)
            end
        end
        return stmt
    end

    local inner = {}
    for i = 1, #bodyStmts do
        local s = bodyStmts[i]
        if s.kind == AstKind.Block or (s.body and s.body.scope and s.body.scope.parentScope == loopScope) then
            if s.body and s.body.scope then s.body.scope:setParent(contScope) end
        end
        if s.scope == loopScope and (s.kind == AstKind.LocalVariableDeclaration or s.kind == AstKind.LocalFunctionDeclaration) then
            s.scope = contScope
        end
        inner[i] = rewriteInStmt(s, contScope)
    end

    local out = {}
    if brkFlagId then
        out[#out + 1] = Ast.LocalVariableDeclaration(loopScope, { brkFlagId }, { Ast.BooleanExpression(false) })
    end
    out[#out + 1] = Ast.RepeatStatement(Ast.BooleanExpression(true), Ast.Block(inner, contScope), loopScope)
    if brkFlagId then
        local chkScope = Scope:new(loopScope)
        chkScope:addReferenceToHigherScope(loopScope, brkFlagId)
        out[#out + 1] = Ast.IfStatement(
            Ast.VariableExpression(loopScope, brkFlagId),
            Ast.Block({ Ast.BreakStatement() }, chkScope),
            {},
            nil
        )
    end
    return out
end

local function classifyOuterArgExpr(expr, localDefs)
    if not expr then return nil, nil end
    if expr.kind == AstKind.VariableExpression then
        if expr.scope and expr.scope.isGlobal then
            return "global", expr.scope:getVariableName(expr.id)
        end
        local def = localDefs and localDefs[tostring(expr.scope) .. ":" .. tostring(expr.id)]
        if def then
            return def.kind, def.name
        end
        return nil, nil
    end
    if expr.kind == AstKind.OrExpression then
        if expr.lhs.kind == AstKind.AndExpression then
            return "env", nil
        elseif expr.rhs.kind == AstKind.IndexExpression then
            return "unpack", nil
        else
            local lk, ln = classifyOuterArgExpr(expr.lhs, localDefs)
            local rk, rn = classifyOuterArgExpr(expr.rhs, localDefs)
            if rk == "global" and rn == "_ENV" then
                return "env", nil
            elseif (lk == "global" and ln == "unpack") or expr.rhs.kind == AstKind.IndexExpression then
                return "unpack", nil
            end
        end
    elseif expr.kind == AstKind.TableConstructorExpression then
        return "arg", nil
    end
    return nil, nil
end

local function buildBlockLocalArgDefs(stmts, maxIdx)
    local defs = {}
    local pureSetup = true
    for idx = 1, maxIdx do
        local s = stmts[idx]
        if s.kind == AstKind.LocalVariableDeclaration then
            if s.expressions and #s.expressions > 0 then
                for j = 1, #s.ids do
                    local ex = s.expressions[j]
                    if ex then
                        local k, nm = classifyOuterArgExpr(ex, defs)
                        if k then
                            defs[tostring(s.scope) .. ":" .. tostring(s.ids[j])] = { kind = k, name = nm }
                        elseif ex.kind == AstKind.AndExpression then
                            defs[tostring(s.scope) .. ":" .. tostring(s.ids[j])] = { kind = "partial_env" }
                        elseif ex.kind ~= AstKind.NilExpression then
                            pureSetup = false
                        end
                    end
                end
            end
        elseif s.kind == AstKind.AssignmentStatement then
            for j = 1, #s.lhs do
                local lv = s.lhs[j]
                local ex = s.rhs[j]
                if lv.kind == AstKind.AssignmentVariable and not lv.scope.isGlobal and ex then
                    local k, nm = classifyOuterArgExpr(ex, defs)
                    if k then
                        defs[tostring(lv.scope) .. ":" .. tostring(lv.id)] = { kind = k, name = nm }
                    elseif ex.kind == AstKind.AndExpression then
                        defs[tostring(lv.scope) .. ":" .. tostring(lv.id)] = { kind = "partial_env" }
                    elseif ex.kind ~= AstKind.NilExpression then
                        pureSetup = false
                    end
                else
                    pureSetup = false
                end
            end
        elseif s.kind == AstKind.IfStatement and #s.elseifs == 0 and not s.elsebody then
            local wroteEnv = false
            local wroteUnpack = false
            for _, bs in ipairs(s.body.statements) do
                if bs.kind == AstKind.AssignmentStatement and #bs.lhs == 1 and #bs.rhs == 1
                    and bs.lhs[1].kind == AstKind.AssignmentVariable and not bs.lhs[1].scope.isGlobal then
                    local vk = tostring(bs.lhs[1].scope) .. ":" .. tostring(bs.lhs[1].id)
                    local r = bs.rhs[1]
                    if r.kind == AstKind.VariableExpression and r.scope.isGlobal and r.scope:getVariableName(r.id) == "_ENV" then
                        defs[vk] = { kind = "env" }
                        wroteEnv = true
                    elseif r.kind == AstKind.IndexExpression then
                        defs[vk] = { kind = "unpack" }
                        wroteUnpack = true
                    end
                end
            end
            if not wroteEnv and not wroteUnpack then
                local condVar = s.condition
                if condVar.kind == AstKind.VariableExpression and not condVar.scope.isGlobal then
                    local vk = tostring(condVar.scope) .. ":" .. tostring(condVar.id)
                    if defs[vk] and defs[vk].name == "getfenv" then
                        defs[vk] = { kind = "partial_env" }
                    else
                        pureSetup = false
                    end
                else
                    pureSetup = false
                end
            end
        else
            pureSetup = false
        end
    end
    return defs, pureSetup
end

local function extractThreeArgInnerClosure(fnNode)
    for _, st in ipairs(fnNode.body.statements) do
        if st.kind == AstKind.LocalFunctionDeclaration then
            return st
        elseif st.kind == AstKind.LocalVariableDeclaration and st.expressions then
            for _, ex in ipairs(st.expressions) do
                if ex.kind == AstKind.FunctionLiteralExpression then
                    return ex
                end
            end
        elseif st.kind == AstKind.AssignmentStatement then
            for _, ex in ipairs(st.rhs) do
                if ex.kind == AstKind.FunctionLiteralExpression then
                    return ex
                end
            end
        end
    end
    return nil
end

local function matchCffContainer(block, globalScope)
    local stmts = block.statements
    if #stmts == 0 then return nil end
    local retStmt = stmts[#stmts]
    if retStmt.kind ~= AstKind.ReturnStatement or #retStmt.args ~= 1 then return nil end
    local outerCall = retStmt.args[1]
    if outerCall.kind ~= AstKind.FunctionCallExpression then return nil end
    local fnNode = outerCall.base
    if fnNode.kind == AstKind.VariableExpression and not fnNode.scope.isGlobal then
        local fSc, fId = fnNode.scope, fnNode.id
        for idx = #stmts - 1, 1, -1 do
            local ps = stmts[idx]
            if ps.kind == AstKind.LocalVariableDeclaration and ps.scope == fSc then
                for j = 1, #ps.ids do
                    if ps.ids[j] == fId and ps.expressions and ps.expressions[j] then
                        if ps.expressions[j].kind == AstKind.FunctionLiteralExpression then
                            fnNode = ps.expressions[j]
                        end
                        break
                    end
                end
                if fnNode.kind == AstKind.FunctionLiteralExpression then break end
            elseif ps.kind == AstKind.LocalFunctionDeclaration and ps.scope == fSc and ps.id == fId then
                fnNode = Ast.FunctionLiteralExpression(ps.args, ps.body)
                break
            elseif ps.kind == AstKind.AssignmentStatement then
                for j = 1, #ps.lhs do
                    if ps.lhs[j].kind == AstKind.AssignmentVariable
                        and ps.lhs[j].scope == fSc and ps.lhs[j].id == fId and ps.rhs[j] then
                        if ps.rhs[j].kind == AstKind.FunctionLiteralExpression then
                            fnNode = ps.rhs[j]
                        elseif ps.rhs[j].kind == AstKind.VariableExpression and not ps.rhs[j].scope.isGlobal then
                            fSc, fId = ps.rhs[j].scope, ps.rhs[j].id
                        end
                        break
                    end
                end
                if fnNode.kind == AstKind.FunctionLiteralExpression then break end
            end
        end
    end
    if fnNode.kind ~= AstKind.FunctionLiteralExpression then return nil end
    if #outerCall.args ~= 11 or #fnNode.args < 23 then return nil end
    if #fnNode.body.statements < 2 then return nil end

    local innerRet = fnNode.body.statements[#fnNode.body.statements]
    if innerRet.kind ~= AstKind.ReturnStatement or #innerRet.args ~= 1 then
        return nil
    end

    local cffScope = fnNode.body.scope
    local helperBindings = {}
    for sIdx = 1, #fnNode.body.statements - 1 do
        local st = fnNode.body.statements[sIdx]
        if st.kind == AstKind.AssignmentStatement then
            if #st.lhs ~= #st.rhs then return nil end
            for i = 1, #st.lhs do
                local lhs = st.lhs[i]
                if lhs.kind == AstKind.AssignmentVariable and lhs.scope == cffScope then
                    helperBindings[#helperBindings + 1] = { vid = lhs.id, rhs = st.rhs[i] }
                elseif lhs.kind == AstKind.AssignmentIndexing
                    and lhs.base.kind == AstKind.VariableExpression
                    and lhs.base.scope == cffScope then
                else
                    return nil
                end
            end
        elseif st.kind == AstKind.LocalVariableDeclaration and st.scope == cffScope then
            if st.expressions then
                for i = 1, #st.ids do
                    if st.expressions[i] then
                        helperBindings[#helperBindings + 1] = { vid = st.ids[i], rhs = st.expressions[i] }
                    end
                end
            end
        elseif st.kind == AstKind.LocalFunctionDeclaration and st.scope == cffScope then
            helperBindings[#helperBindings + 1] = {
                vid = st.id,
                rhs = Ast.FunctionLiteralExpression(st.args, st.body),
            }
        else
            return nil
        end
    end
    if #helperBindings < 11 then
        return nil
    end

    local localDefs, pureOuterSetup = buildBlockLocalArgDefs(stmts, #stmts - 1)
    local info = {
        cffScope = cffScope,
        globalScope = globalScope,
        createClosureArity = {},
        cffAliases = {},
        regVarLookup = {},
        pureOuterSetup = pureOuterSetup,
    }

    for i = 1, 11 do
        local param = fnNode.args[i]
        local arg = outerCall.args[i]
        if param.kind ~= AstKind.VariableExpression or param.scope ~= cffScope then
            return nil
        end
        local akind, gname = classifyOuterArgExpr(arg, localDefs)
        if akind == "env" then
            info.envVar = param.id
        elseif akind == "unpack" then
            info.unpackVar = param.id
        elseif akind == "arg" then
            info.argVar = param.id
        elseif akind == "global" then
            if gname == "newproxy" then info.newproxyVar = param.id
            elseif gname == "setmetatable" then info.setmetatableVar = param.id
            elseif gname == "getmetatable" then info.getmetatableVar = param.id
            elseif gname == "select" then info.selectVar = param.id
            elseif gname == "tonumber" then info.tonumberVar = param.id
            elseif gname == "error" then info.errorVar = param.id
            elseif gname == "getfenv" then info.getfenvVar = param.id
            elseif gname == "setfenv" then info.setfenvVar = param.id
            end
        end
    end

    if not info.envVar or not info.unpackVar or not info.argVar or not info.selectVar then
        return nil
    end

    local emptyTables = {}
    local threeArgFns = {}

    for i = 1, #helperBindings do
        local vid = helperBindings[i].vid
        local rhs = helperBindings[i].rhs
        if rhs.kind == AstKind.VariableExpression and rhs.scope == cffScope then
            info.cffAliases[vid] = info.cffAliases[rhs.id] or rhs.id
        end
    end

    for i = 1, #helperBindings do
        local vid = helperBindings[i].vid
        local rhs = helperBindings[i].rhs
        if rhs.kind == AstKind.NumberExpression and rhs.value == 0 then
            info.currentUpvalId = vid
        elseif rhs.kind == AstKind.TableConstructorExpression and #rhs.entries == 0 then
            emptyTables[#emptyTables + 1] = vid
        elseif rhs.kind == AstKind.FunctionLiteralExpression then
            local nargs = #rhs.args
            if nargs == 5 and rhs.args[1].kind == AstKind.VariableExpression then
                local hasWhile = false
                for _, s in ipairs(rhs.body.statements) do
                    if s.kind == AstKind.WhileStatement then
                        hasWhile = true
                        info.whileStmt = s
                    end
                end
                if hasWhile then
                    info.containerFuncVar = vid
                    info.containerFunc = rhs
                    info.containerScope = rhs.body.scope
                    info.posVar = { [rhs.args[1].id] = true }
                    info.argsVar = { [rhs.args[2].id] = true }
                    info.currentUpvaluesVar = { [rhs.args[3].id] = true }
                    info.detectGcCollectVar = { [rhs.args[4].id] = true }
                    info.currentEnvVar = { [rhs.args[5].id] = true }
                    for _, s in ipairs(rhs.body.statements) do
                        if s == info.whileStmt then break end
                        if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                            and s.lhs[1].kind == AstKind.AssignmentVariable and s.lhs[1].scope == info.containerScope
                            and s.rhs[1].kind == AstKind.VariableExpression and s.rhs[1].scope == info.containerScope then
                            local srcId, dstId = s.rhs[1].id, s.lhs[1].id
                            if info.posVar[srcId] then info.posVar[dstId] = true
                            elseif info.argsVar[srcId] then info.argsVar[dstId] = true
                            elseif info.currentUpvaluesVar[srcId] then info.currentUpvaluesVar[dstId] = true
                            elseif info.detectGcCollectVar[srcId] then info.detectGcCollectVar[dstId] = true
                            elseif info.currentEnvVar[srcId] then info.currentEnvVar[dstId] = true
                            end
                        elseif s.kind == AstKind.LocalVariableDeclaration and s.scope == info.containerScope
                            and s.expressions then
                            for idxD = 1, #s.ids do
                                local ex = s.expressions[idxD]
                                if ex and ex.kind == AstKind.VariableExpression and ex.scope == info.containerScope then
                                    local srcId, dstId = ex.id, s.ids[idxD]
                                    if info.posVar[srcId] then info.posVar[dstId] = true
                                    elseif info.argsVar[srcId] then info.argsVar[dstId] = true
                                    elseif info.currentUpvaluesVar[srcId] then info.currentUpvaluesVar[dstId] = true
                                    elseif info.detectGcCollectVar[srcId] then info.detectGcCollectVar[dstId] = true
                                    elseif info.currentEnvVar[srcId] then info.currentEnvVar[dstId] = true
                                    end
                                end
                            end
                        end
                    end
                end
            elseif nargs == 0 then
                info.allocUpvalFunction = vid
                for _, s in ipairs(rhs.body.statements) do
                    if s.kind == AstKind.AssignmentStatement and #s.lhs >= 1 then
                        local idxLhs = s.lhs[1]
                        if idxLhs and idxLhs.kind == AstKind.AssignmentIndexing
                            and idxLhs.base.kind == AstKind.VariableExpression and idxLhs.base.scope == cffScope then
                            info.upvaluesReferenceCountsTable = idxLhs.base.id
                            break
                        end
                    end
                end
            elseif nargs == 1 and rhs.args[1].kind == AstKind.VarargExpression then
                info.packVar = vid
            elseif nargs == 3 and rhs.args[3].kind == AstKind.VarargExpression then
                info.callFunctionVar = vid
            elseif nargs == 3 and rhs.args[3].kind == AstKind.VariableExpression then
                threeArgFns[#threeArgFns + 1] = { vid = vid, fn = rhs }
            elseif nargs == 1 and rhs.args[1].kind == AstKind.VariableExpression then
                local bstmts = {}
                for k = 1, #rhs.body.statements do
                    local bs = rhs.body.statements[k]
                    if not (k == #rhs.body.statements and bs.kind == AstKind.ReturnStatement and #bs.args == 0) then
                        bstmts[#bstmts + 1] = bs
                    end
                end
                local hasWhile, hasFor, hasIf = false, false, false
                for _, bs in ipairs(bstmts) do
                    if bs.kind == AstKind.WhileStatement then hasWhile = true
                    elseif bs.kind == AstKind.ForStatement then hasFor = true
                    elseif bs.kind == AstKind.IfStatement then hasIf = true
                    end
                end
                if #bstmts == 1 and bstmts[1].kind == AstKind.ReturnStatement then
                    info.unpackPackedVar = vid
                elseif hasWhile then
                    info.upvaluesGcFunctionVar = vid
                elseif hasFor then
                    info.upvaluesProxyFunctionVar = vid
                elseif hasIf then
                    info.freeUpvalueFunc = vid
                    visitSub(rhs, function(fnN)
                        if fnN.kind == AstKind.AssignmentIndexing
                            and fnN.base.kind == AstKind.VariableExpression
                            and fnN.base.scope == cffScope
                            and fnN.base.id ~= info.upvaluesReferenceCountsTable then
                            info.upvaluesTable = fnN.base.id
                        end
                    end, nil, globalScope)
                end
            end
        end
    end

    if not info.upvaluesTable then
        for _, tvid in ipairs(emptyTables) do
            if tvid ~= info.upvaluesReferenceCountsTable then
                info.upvaluesTable = tvid
            end
        end
    end

    for _, item in ipairs(threeArgFns) do
        local innerFn = extractThreeArgInnerClosure(item.fn)
        if innerFn then
            if #innerFn.args == 1 and innerFn.args[1].kind == AstKind.VarargExpression then
                info.createVarargClosureVar = item.vid
            else
                info.createClosureArity[item.vid] = #innerFn.args
            end
        end
    end

    if not info.containerFunc or not info.whileStmt or not info.packVar
        or not info.unpackPackedVar or not info.callFunctionVar
        or not info.upvaluesTable then
        return nil
    end

    local cStmts = info.containerFunc.body.statements
    local finalRet = cStmts[#cStmts]
    if not finalRet or finalRet.kind ~= AstKind.ReturnStatement or #finalRet.args ~= 1 then
        return nil
    end
    local finalUnpack = finalRet.args[1]
    if finalUnpack.kind ~= AstKind.FunctionCallExpression or #finalUnpack.args ~= 1
        or finalUnpack.args[1].kind ~= AstKind.VariableExpression
        or finalUnpack.args[1].scope ~= info.containerScope then
        return nil
    end
    info.returnVar = finalUnpack.args[1].id

    for _, s in ipairs(cStmts) do
        if s == info.whileStmt then break end
        if s.kind == AstKind.LocalVariableDeclaration and s.scope == info.containerScope then
            if #s.ids == 1 and s.expressions and #s.expressions == 1
                and s.expressions[1].kind == AstKind.TableConstructorExpression then
                info.spillVarId = s.ids[1]
            else
                for _, id in ipairs(s.ids) do
                    if id ~= info.returnVar
                        and not info.posVar[id]
                        and not info.argsVar[id]
                        and not info.currentUpvaluesVar[id]
                        and not info.detectGcCollectVar[id]
                        and not info.currentEnvVar[id] then
                        info.regVarLookup[id] = true
                    end
                end
            end
        elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
            and s.lhs[1].kind == AstKind.AssignmentVariable and s.lhs[1].scope == info.containerScope
            and s.rhs[1].kind == AstKind.TableConstructorExpression and #s.rhs[1].entries == 0
            and not info.spillVarId then
            info.spillVarId = s.lhs[1].id
            info.regVarLookup[info.spillVarId] = nil
        end
    end

    info.dispatchScopes = {}
    visitSub(info.whileStmt, function(wn)
        if wn.kind == AstKind.FunctionLiteralExpression
            or wn.kind == AstKind.LocalFunctionDeclaration
            or wn.kind == AstKind.FunctionDeclaration then
            return nil, true
        end
        if wn.kind == AstKind.LocalVariableDeclaration and wn.scope
            and wn.scope ~= info.containerScope and wn.scope ~= cffScope and not wn.scope.isGlobal then
            info.dispatchScopes[wn.scope] = true
        end
        if wn.body and wn.body.scope and wn.body.scope ~= info.containerScope and not wn.body.scope.isGlobal then
            info.dispatchScopes[wn.body.scope] = true
        end
        if wn.elsebody and wn.elsebody.scope and wn.elsebody.scope ~= info.containerScope and not wn.elsebody.scope.isGlobal then
            info.dispatchScopes[wn.elsebody.scope] = true
        end
    end, nil, globalScope)

    local bootCall = innerRet.args[1]
    if bootCall.kind ~= AstKind.FunctionCallExpression
        or bootCall.base.kind ~= AstKind.FunctionCallExpression then
        return nil
    end
    local createBoot = bootCall.base
    local bootOk = false
    if info.createVarargClosureVar and isVarRef(createBoot.base, cffScope, info.createVarargClosureVar) then
        bootOk = true
    elseif createBoot.base.kind == AstKind.FunctionLiteralExpression and #createBoot.base.args == 3 then
        local innerBootFn = extractThreeArgInnerClosure(createBoot.base)
        if innerBootFn and #innerBootFn.args == 1 and innerBootFn.args[1].kind == AstKind.VarargExpression then
            bootOk = true
        end
    end
    if not bootOk or #createBoot.args < 2 then
        return nil
    end
    if createBoot.args[1].kind ~= AstKind.NumberExpression
        or createBoot.args[2].kind ~= AstKind.TableConstructorExpression then
        return nil
    end
    info.startBlockId = createBoot.args[1].value
    info.topUpvalCount = #createBoot.args[2].entries

    return info
end

local function regKeyOfNode(node, info)
    if not node then return nil end
    if node.kind == AstKind.VariableExpression or node.kind == AstKind.AssignmentVariable then
        if node.scope == info.containerScope then
            local id = node.id
            if id ~= info.returnVar
                and id ~= info.spillVarId
                and not info.posVar[id]
                and not info.argsVar[id]
                and not info.currentUpvaluesVar[id]
                and not info.detectGcCollectVar[id]
                and not info.currentEnvVar[id] then
                return "r_" .. tostring(id)
            end
            return nil
        end
        if info.dispatchScopes and info.dispatchScopes[node.scope] then
            return "d_" .. tostring(node.scope) .. "_" .. tostring(node.id)
        end
    end
    if (node.kind == AstKind.IndexExpression or node.kind == AstKind.AssignmentIndexing)
        and info.spillVarId
        and isVarRef(node.base, info.containerScope, info.spillVarId)
        and node.index.kind == AstKind.NumberExpression then
        return "s_" .. tostring(node.index.value)
    end
    return nil
end

local function extractDispatchLeaves(info)
    local leaves = {}
    local containerScope = info.containerScope
    local posVar = info.posVar

    local function matchPosBound(cond)
        if cond.kind == AstKind.LessThanExpression then
            if isVarRef(cond.lhs, containerScope, posVar) and cond.rhs.kind == AstKind.NumberExpression then
                return "lt", cond.rhs.value
            elseif cond.lhs.kind == AstKind.NumberExpression and isVarRef(cond.rhs, containerScope, posVar) then
                return "gt", cond.lhs.value
            end
        elseif cond.kind == AstKind.GreaterThanExpression then
            if cond.lhs.kind == AstKind.NumberExpression and isVarRef(cond.rhs, containerScope, posVar) then
                return "lt", cond.lhs.value
            elseif isVarRef(cond.lhs, containerScope, posVar) and cond.rhs.kind == AstKind.NumberExpression then
                return "gt", cond.rhs.value
            end
        end
        return nil, nil
    end

    local function resolveDispatchIf(blk)
        local n = #blk.statements
        if n == 0 then return nil, nil, nil, nil end
        local last = blk.statements[n]
        if last.kind ~= AstKind.IfStatement or not last.elsebody then
            return nil, nil, nil, nil
        end
        local tempMap = {}
        local function expandDispExpr(e, depth)
            if not e or depth > 6 then return e end
            if e.kind == AstKind.VariableExpression and not isVarRef(e, containerScope, posVar) then
                local rk = regKeyOfNode(e, info)
                local mapped = rk and tempMap[rk] or nil
                if mapped then return expandDispExpr(mapped, depth + 1) end
            elseif e.kind == AstKind.LessThanExpression then
                return Ast.LessThanExpression(expandDispExpr(e.lhs, depth + 1), expandDispExpr(e.rhs, depth + 1))
            elseif e.kind == AstKind.GreaterThanExpression then
                return Ast.GreaterThanExpression(expandDispExpr(e.lhs, depth + 1), expandDispExpr(e.rhs, depth + 1))
            end
            return e
        end
        for i = 1, n - 1 do
            local s = blk.statements[i]
            if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1 then
                local lk = regKeyOfNode(s.lhs[1], info)
                if not lk then return nil, nil, nil, nil end
                local r = s.rhs[1]
                if r.kind == AstKind.NilExpression then
                    tempMap[lk] = nil
                elseif r.kind == AstKind.NumberExpression
                    or r.kind == AstKind.LessThanExpression
                    or r.kind == AstKind.GreaterThanExpression
                    or isVarRef(r, containerScope, posVar)
                    or regKeyOfNode(r, info) ~= nil then
                    tempMap[lk] = expandDispExpr(r, 0)
                else
                    return nil, nil, nil, nil
                end
            elseif s.kind == AstKind.LocalVariableDeclaration
                and (s.scope == containerScope or info.dispatchScopes[s.scope]) then
                if s.expressions and #s.expressions > 0 then
                    for j = 1, #s.ids do
                        local ex = s.expressions[j]
                        local lk = s.scope == containerScope and ("r_" .. tostring(s.ids[j]))
                            or ("d_" .. tostring(s.scope) .. "_" .. tostring(s.ids[j]))
                        if not ex or ex.kind == AstKind.NilExpression then
                            tempMap[lk] = nil
                        elseif ex.kind == AstKind.NumberExpression
                            or ex.kind == AstKind.LessThanExpression
                            or ex.kind == AstKind.GreaterThanExpression
                            or isVarRef(ex, containerScope, posVar)
                            or regKeyOfNode(ex, info) ~= nil then
                            tempMap[lk] = expandDispExpr(ex, 0)
                        else
                            return nil, nil, nil, nil
                        end
                    end
                end
            else
                return nil, nil, nil, nil
            end
        end
        local dir, bound = matchPosBound(expandDispExpr(last.condition, 0))
        if not dir then return nil, nil, nil, nil end
        return last, dir, bound, expandDispExpr
    end

    local function walkDispatch(blk, lo, hi)
        local ifs, dir, bound, expandDispExpr = resolveDispatchIf(blk)
        if ifs and dir then
            if #ifs.elseifs > 0 then
                local curLo = lo
                if dir ~= "lt" then return nil end
                walkDispatch(ifs.body, curLo, bound)
                curLo = bound
                for _, eif in ipairs(ifs.elseifs) do
                    local edir, ebound = matchPosBound(expandDispExpr(eif.condition, 0))
                    if edir ~= "lt" then return nil end
                    walkDispatch(eif.body, curLo, ebound)
                    curLo = ebound
                end
                walkDispatch(ifs.elsebody, curLo, hi)
                return
            else
                if dir == "lt" then
                    walkDispatch(ifs.body, lo, bound)
                    walkDispatch(ifs.elsebody, bound, hi)
                else
                    walkDispatch(ifs.elsebody, lo, bound)
                    walkDispatch(ifs.body, bound, hi)
                end
                return
            end
        end
        leaves[#leaves + 1] = {
            idx = #leaves + 1,
            lo = lo,
            hi = hi,
            rawBlock = blk,
        }
    end

    walkDispatch(info.whileStmt.body, -math.huge, math.huge)

    local function leafForId(blockId)
        local l, r = 1, #leaves
        while l <= r do
            local m = math.floor((l + r) / 2)
            local leaf = leaves[m]
            if blockId <= leaf.lo then
                r = m - 1
            elseif blockId >= leaf.hi then
                l = m + 1
            else
                return m
            end
        end
        return nil
    end

    return leaves, leafForId
end

local function normalizeLeafStatements(rawStmts, info, leafForId)
    local flat = {}
    for _, s in ipairs(rawStmts) do
        if s.kind == AstKind.AssignmentStatement and #s.lhs == #s.rhs and #s.lhs > 1 then
            for j = 1, #s.lhs do
                flat[#flat + 1] = Ast.AssignmentStatement({ s.lhs[j] }, { s.rhs[j] })
            end
        elseif s.kind == AstKind.LocalVariableDeclaration
            and (s.scope == info.containerScope or (info.dispatchScopes and info.dispatchScopes[s.scope])) then
            if s.expressions and #s.expressions > 0 then
                for j = 1, #s.ids do
                    local ex = s.expressions[j] or Ast.NilExpression()
                    flat[#flat + 1] = Ast.AssignmentStatement({ Ast.AssignmentVariable(s.scope, s.ids[j]) }, { ex })
                end
            end
        else
            flat[#flat + 1] = s
        end
    end

    local constNumInReg = {}
    local envLookupInReg = {}
    local currentEnvAlias = {}
    local branchInVar = {}
    local pendingAndInVar = {}
    local pendingPosAnd = nil
    local pendingPosCond = nil
    local term = nil
    local body = {}

    local function varNodeKey(e)
        if not e then return nil end
        if e.kind == AstKind.VariableExpression or e.kind == AstKind.AssignmentVariable then
            return tostring(e.scope) .. ":" .. tostring(e.id)
        end
        return regKeyOfNode(e, info)
    end

    local function isCurrentEnvExpr(e)
        if not e then return false end
        if isVarRef(e, info.containerScope, info.currentEnvVar) then return true end
        local rk = regKeyOfNode(e, info)
        return rk ~= nil and currentEnvAlias[rk] == true
    end

    local function evalNumOrReg(expr)
        if not expr then return nil end
        if expr.kind == AstKind.NumberExpression then
            return expr.value
        end
        local rk = regKeyOfNode(expr, info)
        if rk and constNumInReg[rk] ~= nil then
            return constNumInReg[rk]
        end
        return nil
    end

    local function evalSingleBranchIfTarget(blk)
        if not blk or #blk.statements == 0 then return nil, nil end
        local localNums = {}
        local lastVk, lastNum = nil, nil
        for i = 1, #blk.statements do
            local bs = blk.statements[i]
            if bs.kind ~= AstKind.AssignmentStatement or #bs.lhs ~= 1 or #bs.rhs ~= 1 then
                return nil, nil
            end
            local lk = varNodeKey(bs.lhs[1])
            if not lk or isVarRef(bs.lhs[1], info.containerScope, info.posVar) then
                return nil, nil
            end
            local num = evalNumOrReg(bs.rhs[1])
            if num == nil then
                local rk = varNodeKey(bs.rhs[1])
                if rk and localNums[rk] ~= nil then
                    num = localNums[rk]
                end
            end
            if num == nil then
                return nil, nil
            end
            localNums[lk] = num
            lastVk, lastNum = lk, num
        end
        return lastVk, lastNum
    end

    local function evalSingleBranchPosTarget(blk)
        if not blk or #blk.statements == 0 then return nil end
        local localNums = {}
        local posNum = nil
        for i = 1, #blk.statements do
            local bs = blk.statements[i]
            if bs.kind ~= AstKind.AssignmentStatement or #bs.lhs ~= 1 or #bs.rhs ~= 1 then
                return nil
            end
            local num = evalNumOrReg(bs.rhs[1])
            if num == nil then
                local rk = varNodeKey(bs.rhs[1])
                if rk and localNums[rk] ~= nil then
                    num = localNums[rk]
                end
            end
            if num == nil then return nil end
            if isVarRef(bs.lhs[1], info.containerScope, info.posVar) then
                posNum = num
            else
                local lk = varNodeKey(bs.lhs[1])
                if not lk then return nil end
                localNums[lk] = num
            end
        end
        return posNum
    end

    local function removeBodyStmt(targetStmt)
        if not targetStmt then return end
        for idx = #body, 1, -1 do
            if body[idx] == targetStmt then
                table.remove(body, idx)
                return
            end
        end
    end

    for _, s in ipairs(flat) do
        local handledPos = false
        if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1 then
            local lhs, rhs = s.lhs[1], s.rhs[1]
            if isVarRef(lhs, info.containerScope, info.posVar) then
                handledPos = true
                local rhsRk = regKeyOfNode(rhs, info)
                local rhsVk = varNodeKey(rhs)
                if rhs.kind == AstKind.NilExpression
                    or (rhs.kind == AstKind.IndexExpression and isCurrentEnvExpr(rhs.base))
                    or (rhsRk and envLookupInReg[rhsRk]) then
                    term = { kind = "return" }
                    pendingPosAnd = nil
                elseif rhsVk and branchInVar[rhsVk] then
                    local br = branchInVar[rhsVk]
                    removeBodyStmt(br.if2)
                    removeBodyStmt(br.if1)
                    removeBodyStmt(br.stmt)
                    removeBodyStmt(br.declStmt)
                    local cPos = br.condPos or #body
                    if cPos > #body then cPos = #body end
                    term = {
                        kind = "branch",
                        cond = br.cond,
                        condPos = cPos,
                        trueTarget = leafForId(br.tId),
                        falseTarget = leafForId(br.fId),
                    }
                    pendingPosAnd = nil
                    pendingPosCond = nil
                elseif rhsVk and pendingAndInVar[rhsVk] then
                    pendingPosAnd = pendingAndInVar[rhsVk]
                    pendingPosCond = nil
                elseif rhs.kind == AstKind.OrExpression then
                    local andT = rhs.lhs.kind == AstKind.AndExpression and evalNumOrReg(rhs.lhs.rhs) or nil
                    local orF = evalNumOrReg(rhs.rhs)
                    if andT and orF then
                        term = {
                            kind = "branch",
                            cond = rhs.lhs.lhs,
                            condPos = #body,
                            trueTarget = leafForId(andT),
                            falseTarget = leafForId(orF),
                        }
                        pendingPosAnd = nil
                    elseif isVarRef(rhs.lhs, info.containerScope, info.posVar) and pendingPosAnd then
                        local fId = evalNumOrReg(rhs.rhs)
                        if fId then
                            term = {
                                kind = "branch",
                                cond = pendingPosAnd.cond,
                                condPos = pendingPosAnd.condPos,
                                trueTarget = leafForId(pendingPosAnd.tId),
                                falseTarget = leafForId(fId),
                            }
                            pendingPosAnd = nil
                            pendingPosCond = nil
                        end
                    elseif varNodeKey(rhs.lhs) and pendingAndInVar[varNodeKey(rhs.lhs)] then
                        local pa = pendingAndInVar[varNodeKey(rhs.lhs)]
                        local fId = evalNumOrReg(rhs.rhs)
                        if fId then
                            removeBodyStmt(pa.if1)
                            removeBodyStmt(pa.stmt)
                            local cPos = pa.condPos or #body
                            if cPos > #body then cPos = #body end
                            term = {
                                kind = "branch",
                                cond = pa.cond,
                                condPos = cPos,
                                trueTarget = leafForId(pa.tId),
                                falseTarget = leafForId(fId),
                            }
                            pendingPosAnd = nil
                            pendingPosCond = nil
                        end
                    end
                elseif rhs.kind == AstKind.AndExpression then
                    local tId = evalNumOrReg(rhs.rhs)
                    if tId then
                        pendingPosAnd = { cond = rhs.lhs, condPos = #body, tId = tId }
                        pendingPosCond = nil
                    end
                else
                    local targetId = evalNumOrReg(rhs)
                    if targetId then
                        term = { kind = "goto", target = leafForId(targetId) }
                        pendingPosAnd = nil
                        pendingPosCond = nil
                    else
                        pendingPosCond = { cond = rhs, condPos = #body }
                    end
                end
            elseif isVarRef(rhs, info.containerScope, info.posVar) then
                local rk = regKeyOfNode(lhs, info)
                if rk then
                    constNumInReg[rk] = nil
                    envLookupInReg[rk] = nil
                    currentEnvAlias[rk] = nil
                    handledPos = true
                end
            else
                local rk = regKeyOfNode(lhs, info)
                local dstVk = varNodeKey(lhs)
                local srcVk = varNodeKey(rhs)
                local srcRk = regKeyOfNode(rhs, info)
                if dstVk then
                    if rhs.kind == AstKind.AndExpression then
                        local tVal = evalNumOrReg(rhs.rhs)
                        if tVal then
                            pendingAndInVar[dstVk] = {
                                cond = rhs.lhs,
                                condPos = #body,
                                tId = tVal,
                                if1 = s,
                            }
                            branchInVar[dstVk] = nil
                        else
                            pendingAndInVar[dstVk] = nil
                            branchInVar[dstVk] = nil
                        end
                    elseif rhs.kind == AstKind.OrExpression then
                        local fVal = evalNumOrReg(rhs.rhs)
                        local lhsVk = varNodeKey(rhs.lhs)
                        local pa = lhsVk and pendingAndInVar[lhsVk] or nil
                        if rhs.lhs.kind == AstKind.AndExpression then
                            local tVal = evalNumOrReg(rhs.lhs.rhs)
                            if tVal and fVal then
                                branchInVar[dstVk] = {
                                    cond = rhs.lhs.lhs,
                                    condPos = #body,
                                    tId = tVal,
                                    fId = fVal,
                                    if2 = s,
                                }
                                pendingAndInVar[dstVk] = nil
                            else
                                pendingAndInVar[dstVk] = nil
                                branchInVar[dstVk] = nil
                            end
                        elseif pa and fVal then
                            branchInVar[dstVk] = {
                                cond = pa.cond,
                                condPos = pa.condPos,
                                tId = pa.tId,
                                fId = fVal,
                                if1 = pa.if1,
                                if2 = s,
                            }
                            if dstVk ~= lhsVk then
                                pendingAndInVar[dstVk] = nil
                            else
                                pendingAndInVar[dstVk] = nil
                            end
                        else
                            pendingAndInVar[dstVk] = nil
                            branchInVar[dstVk] = nil
                        end
                    elseif srcVk and srcVk ~= dstVk then
                        pendingAndInVar[dstVk] = pendingAndInVar[srcVk]
                        branchInVar[dstVk] = branchInVar[srcVk]
                    elseif not srcVk then
                        pendingAndInVar[dstVk] = nil
                        branchInVar[dstVk] = nil
                    end
                end
                if rk then
                    if rhs.kind == AstKind.NumberExpression then
                        constNumInReg[rk] = rhs.value
                        envLookupInReg[rk] = nil
                        currentEnvAlias[rk] = nil
                    elseif srcRk and constNumInReg[srcRk] ~= nil then
                        constNumInReg[rk] = constNumInReg[srcRk]
                        envLookupInReg[rk] = nil
                        currentEnvAlias[rk] = nil
                    elseif isCurrentEnvExpr(rhs) or (srcRk and currentEnvAlias[srcRk]) then
                        constNumInReg[rk] = nil
                        envLookupInReg[rk] = nil
                        currentEnvAlias[rk] = true
                    elseif (rhs.kind == AstKind.IndexExpression and isCurrentEnvExpr(rhs.base))
                        or (srcRk and envLookupInReg[srcRk]) then
                        constNumInReg[rk] = nil
                        envLookupInReg[rk] = true
                        currentEnvAlias[rk] = nil
                    else
                        constNumInReg[rk] = nil
                        envLookupInReg[rk] = nil
                        currentEnvAlias[rk] = nil
                    end
                end
            end
        elseif s.kind == AstKind.IfStatement and #s.elseifs == 0 and not s.elsebody then
            local posTarget = evalSingleBranchPosTarget(s.body)
            if posTarget and isVarRef(s.condition, info.containerScope, info.posVar) and pendingPosCond then
                handledPos = true
                pendingPosAnd = {
                    cond = pendingPosCond.cond,
                    condPos = pendingPosCond.condPos,
                    tId = posTarget,
                }
                pendingPosCond = nil
            elseif posTarget and s.condition.kind == AstKind.NotExpression
                and isVarRef(s.condition.rhs, info.containerScope, info.posVar) and pendingPosAnd then
                handledPos = true
                local cPos = pendingPosAnd.condPos or #body
                if cPos > #body then cPos = #body end
                term = {
                    kind = "branch",
                    cond = pendingPosAnd.cond,
                    condPos = cPos,
                    trueTarget = leafForId(pendingPosAnd.tId),
                    falseTarget = leafForId(posTarget),
                }
                pendingPosAnd = nil
                pendingPosCond = nil
            else
                local targetVk, targetVal = evalSingleBranchIfTarget(s.body)
                if targetVk and targetVal then
                    if s.condition.kind == AstKind.NotExpression then
                        local innerVk = varNodeKey(s.condition.rhs)
                        local pa = innerVk and pendingAndInVar[innerVk] or nil
                        if pa and innerVk == targetVk then
                            branchInVar[targetVk] = {
                                cond = pa.cond,
                                condPos = pa.condPos,
                                tId = pa.tId,
                                fId = targetVal,
                                if1 = pa.if1,
                                if2 = s,
                            }
                            pendingAndInVar[targetVk] = nil
                        elseif isVarRef(s.condition.rhs, info.containerScope, info.posVar) and pendingPosAnd then
                            branchInVar[targetVk] = {
                                cond = pendingPosAnd.cond,
                                condPos = pendingPosAnd.condPos,
                                tId = pendingPosAnd.tId,
                                fId = targetVal,
                                if1 = pendingPosAnd.if1,
                                if2 = s,
                            }
                            pendingPosAnd = nil
                            pendingPosCond = nil
                        else
                            pendingAndInVar[targetVk] = {
                                cond = s.condition,
                                condPos = #body,
                                tId = targetVal,
                                if1 = s,
                            }
                        end
                    else
                        pendingAndInVar[targetVk] = {
                            cond = s.condition,
                            condPos = #body,
                            tId = targetVal,
                            if1 = s,
                        }
                    end
                else
                    visitSub(s, function(n)
                        if n.kind == AstKind.AssignmentStatement then
                            for _, l in ipairs(n.lhs) do
                                local rk = regKeyOfNode(l, info)
                                if rk then constNumInReg[rk] = nil end
                                local vk = varNodeKey(l)
                                if vk then
                                    pendingAndInVar[vk] = nil
                                    branchInVar[vk] = nil
                                end
                            end
                        end
                    end, nil, info.globalScope)
                end
            end
        elseif s.kind == AstKind.IfStatement and #s.elseifs == 0 and s.elsebody
            and #s.body.statements == 1 and #s.elsebody.statements == 1
            and s.body.statements[1].kind == AstKind.AssignmentStatement
            and s.elsebody.statements[1].kind == AstKind.AssignmentStatement
            and #s.body.statements[1].lhs == 1 and #s.elsebody.statements[1].lhs == 1 then
            local a1, a2 = s.body.statements[1], s.elsebody.statements[1]
            local tVal, fVal = evalNumOrReg(a1.rhs[1]), evalNumOrReg(a2.rhs[1])
            if tVal and fVal then
                if isVarRef(a1.lhs[1], info.containerScope, info.posVar)
                    and isVarRef(a2.lhs[1], info.containerScope, info.posVar) then
                    handledPos = true
                    term = {
                        kind = "branch",
                        cond = s.condition,
                        condPos = #body,
                        trueTarget = leafForId(tVal),
                        falseTarget = leafForId(fVal),
                    }
                elseif a1.lhs[1].kind == AstKind.AssignmentVariable and a2.lhs[1].kind == AstKind.AssignmentVariable
                    and a1.lhs[1].scope == a2.lhs[1].scope and a1.lhs[1].id == a2.lhs[1].id then
                    local vk = tostring(a1.lhs[1].scope) .. ":" .. tostring(a1.lhs[1].id)
                    local prevDeclPos, prevDeclStmt = nil, nil
                    if #body >= 1 and body[#body].kind == AstKind.LocalVariableDeclaration
                        and #body[#body].ids == 1 and #(body[#body].expressions or {}) == 0
                        and body[#body].scope == a1.lhs[1].scope and body[#body].ids[1] == a1.lhs[1].id then
                        prevDeclPos, prevDeclStmt = #body, body[#body]
                    end
                    branchInVar[vk] = {
                        cond = s.condition,
                        tId = tVal,
                        fId = fVal,
                        stmtPos = #body + 1,
                        stmt = s,
                        declPos = prevDeclPos,
                        declStmt = prevDeclStmt,
                    }
                end
            end
        else
            if s.kind == AstKind.AssignmentStatement then
                for _, l in ipairs(s.lhs) do
                    local rk = regKeyOfNode(l, info)
                    if rk then constNumInReg[rk] = nil end
                end
            elseif COMPOUND_CONSTRUCTORS[s.kind] then
                local rk = regKeyOfNode(s.lhs, info)
                if rk then constNumInReg[rk] = nil end
            end
        end

        if not handledPos then
            body[#body + 1] = s
        end
    end

    return body, term or { kind = "return" }
end

local function isPureInlineExpr(expr, targetScope)
    if not expr then return false end
    local k = expr.kind
    if k == AstKind.NumberExpression or k == AstKind.StringExpression
        or k == AstKind.BooleanExpression or k == AstKind.NilExpression
        or k == AstKind.FunctionLiteralExpression then
        return true
    end
    if k == AstKind.VariableExpression then
        return not expr.scope.isGlobal
    end
    return false
end

local function exprHasCall(expr, globalScope)
    local found = false
    visitSub(expr, function(n)
        if n.kind == AstKind.FunctionLiteralExpression then
            return nil, true
        end
        if n.kind == AstKind.FunctionCallExpression or n.kind == AstKind.PassSelfFunctionCallExpression then
            found = true
        end
    end, nil, globalScope)
    return found
end

local function stmtHasSideEffect(stmt, globalScope)
    if not stmt then return false end
    local k = stmt.kind
    if k == AstKind.FunctionCallStatement or k == AstKind.PassSelfFunctionCallStatement
        or k == AstKind.ReturnStatement or k == AstKind.BreakStatement or k == AstKind.ContinueStatement then
        return true
    end
    if COMPOUND_CONSTRUCTORS[k] then
        return true
    end
    if k == AstKind.AssignmentStatement then
        for _, l in ipairs(stmt.lhs) do
            if l.kind == AstKind.AssignmentIndexing or (l.scope and l.scope.isGlobal) then
                return true
            end
        end
        for _, r in ipairs(stmt.rhs) do
            if exprHasCall(r, globalScope) then return true end
        end
        return false
    end
    if k == AstKind.LocalVariableDeclaration then
        for _, r in ipairs(stmt.expressions or {}) do
            if exprHasCall(r, globalScope) then return true end
        end
        return false
    end
    return true
end

local function isScopeReachable(fromScope, targetScope)
    if not fromScope or not targetScope then return false end
    if targetScope.isGlobal then return true end
    local cur = fromScope
    local guard = 0
    while cur and guard < 512 do
        if cur == targetScope then return true end
        cur = cur.parentScope
        guard = guard + 1
    end
    return false
end

local function rebindScopesInSubtree(root, defaultScope, globalScope)
    visitSub(root, function(n)
        if n.body and n.body.scope and not n.body.scope.isGlobal then
            n.body.scope.variablesFromHigherScopes = {}
            n.body.scope.referenceCounts = {}
        end
        if n.scope and not n.scope.isGlobal then
            n.scope.variablesFromHigherScopes = {}
            n.scope.referenceCounts = {}
        end
    end, nil, globalScope)

    local scopeStack = { defaultScope }
    local pushedAtNode = {}
    visitSub(root, function(n)
        local pushScope = nil
        if n.kind == AstKind.FunctionLiteralExpression or n.kind == AstKind.LocalFunctionDeclaration or n.kind == AstKind.FunctionDeclaration then
            if n.body and n.body.scope then
                pushScope = n.body.scope
            end
        elseif (n.kind == AstKind.ForStatement or n.kind == AstKind.ForInStatement or n.kind == AstKind.Block) and n.scope then
            pushScope = n.scope
        end
        if pushScope and pushScope ~= scopeStack[#scopeStack] then
            if pushScope.parentScope ~= scopeStack[#scopeStack] then
                pushScope.parentScope = scopeStack[#scopeStack]
            end
            scopeStack[#scopeStack + 1] = pushScope
            pushedAtNode[n] = pushScope
        end
        if (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable)
            and n.scope then
            local cur = scopeStack[#scopeStack]
            if isScopeReachable(cur, n.scope) then
                cur:addReferenceToHigherScope(n.scope, n.id)
            end
        end
    end, function(n)
        local ps = pushedAtNode[n]
        if ps and scopeStack[#scopeStack] == ps then
            table.remove(scopeStack)
        end
    end, globalScope)
end

local function computeDominators(entry, nodes, succsOf)
    local rpo = {}
    local visited = {}
    local function dfs(u)
        visited[u] = true
        for _, v in ipairs(succsOf(u)) do
            if not visited[v] then dfs(v) end
        end
        rpo[#rpo + 1] = u
    end
    dfs(entry)

    local order = {}
    local rpoIdx = {}
    for i = #rpo, 1, -1 do
        local u = rpo[i]
        order[#order + 1] = u
        rpoIdx[u] = #order
    end

    local preds = {}
    for _, u in ipairs(order) do preds[u] = {} end
    for _, u in ipairs(order) do
        for _, v in ipairs(succsOf(u)) do
            if preds[v] then
                preds[v][#preds[v] + 1] = u
            end
        end
    end

    local idom = { [entry] = entry }
    local function intersect(b1, b2)
        local f1, f2 = b1, b2
        while f1 ~= f2 do
            while rpoIdx[f1] > rpoIdx[f2] do f1 = idom[f1] end
            while rpoIdx[f2] > rpoIdx[f1] do f2 = idom[f2] end
        end
        return f1
    end

    local changed = true
    while changed do
        changed = false
        for i = 2, #order do
            local u = order[i]
            local newIdom = nil
            for _, p in ipairs(preds[u]) do
                if idom[p] then
                    newIdom = newIdom and intersect(p, newIdom) or p
                end
            end
            if newIdom and idom[u] ~= newIdom then
                idom[u] = newIdom
                changed = true
            end
        end
    end

    local function dominates(a, b)
        if not a or not b or not idom[b] then return false end
        local cur = b
        while cur do
            if cur == a then return true end
            if cur == idom[cur] then break end
            cur = idom[cur]
        end
        return false
    end

    return order, idom, preds, dominates, rpoIdx
end

local function computePostDomOnDag(startNode, regionCheck, forwardSuccs)
    local EXIT = -1
    local postOrder = {}
    local seen = {}

    local function dfs(u)
        if u == EXIT or seen[u] then return end
        seen[u] = true
        for _, v in ipairs(forwardSuccs(u)) do
            local nxt = regionCheck(v) and v or EXIT
            if nxt ~= EXIT and not seen[nxt] then
                dfs(nxt)
            end
        end
        postOrder[#postOrder + 1] = u
    end
    dfs(startNode)

    local rank = { [EXIT] = 1 }
    local nodes = { EXIT }
    for i = 1, #postOrder do
        local u = postOrder[i]
        nodes[#nodes + 1] = u
        rank[u] = #nodes
    end

    local ipdom = { [EXIT] = EXIT }
    local function intersect(a, b)
        local x, y = a, b
        while x ~= y do
            while rank[x] > rank[y] do x = ipdom[x] end
            while rank[y] > rank[x] do y = ipdom[y] end
        end
        return x
    end

    local changed = true
    while changed do
        changed = false
        for i = 2, #nodes do
            local u = nodes[i]
            local succs = forwardSuccs(u)
            local pdom = nil
            if #succs == 0 then
                pdom = EXIT
            else
                for _, v in ipairs(succs) do
                    local nxt = (regionCheck(v) and rank[v]) and v or EXIT
                    if ipdom[nxt] then
                        pdom = pdom and intersect(pdom, nxt) or nxt
                    end
                end
            end
            pdom = pdom or EXIT
            if ipdom[u] ~= pdom then
                ipdom[u] = pdom
                changed = true
            end
        end
    end

    return ipdom, EXIT
end

local function liftContainer(block, info, targetLuaVersion)
    local leaves, leafForId = extractDispatchLeaves(info)
    if #leaves == 0 then return nil end

    local normBlocks = {}
    local function getNormBlock(idx)
        if not idx then return nil end
        if not normBlocks[idx] then
            local body, term = normalizeLeafStatements(leaves[idx].rawBlock.statements, info, leafForId)
            normBlocks[idx] = { idx = idx, rawStmts = body, term = term }
        end
        return normBlocks[idx]
    end

    local topParentScope = block.scope or info.globalScope
    local holderScope = Scope:new(topParentScope)
    local helperVars = {}
    local function getHelperVar(kindName)
        if not helperVars[kindName] then
            helperVars[kindName] = holderScope:addVariable()
        end
        return helperVars[kindName]
    end

    local liftClosure

    local function unwrapNativeCall(factoryFn, proxyArg, resolveCapExpr, currentScope)
        if factoryFn.kind ~= AstKind.FunctionLiteralExpression or #factoryFn.args ~= 3 then
            return nil
        end
        local bstmts = factoryFn.body.statements
        if #bstmts < 2 or bstmts[1].kind ~= AstKind.LocalVariableDeclaration then
            return nil
        end
        local nativeExpr = bstmts[1].expressions and bstmts[1].expressions[1]
        if not nativeExpr then return nil end

        factoryFn.body.scope.parentScope = currentScope

        local proxyParam = factoryFn.args[1]
        local envParam = factoryFn.args[2]
        local valuesParam = factoryFn.args[3]

        local capList = {}
        if proxyArg.kind == AstKind.FunctionCallExpression
            and isVarRef(proxyArg.base, info.cffScope, info.upvaluesProxyFunctionVar)
            and #proxyArg.args == 1 and proxyArg.args[1].kind == AstKind.TableConstructorExpression then
            for i, ent in ipairs(proxyArg.args[1].entries) do
                capList[i] = resolveCapExpr(ent.value)
            end
        end

        local function isSlotIndex(idxExpr)
            if idxExpr.kind == AstKind.IndexExpression
                and isVarRef(idxExpr.base, proxyParam.scope, proxyParam.id)
                and idxExpr.index.kind == AstKind.NumberExpression then
                return idxExpr.index.value
            end
            return nil
        end

        local dummyTop = Ast.TopNode(Ast.Block({ Ast.ReturnStatement({ nativeExpr }) }, currentScope), info.globalScope)
        visitast(dummyTop, nil, function(n, data)
            if n.kind == AstKind.IndexExpression then
                if isVarRef(n.base, envParam.scope, envParam.id) and n.index.kind == AstKind.StringExpression then
                    local _, gid = info.globalScope:resolve(n.index.value)
                    data.scope:addReferenceToHigherScope(info.globalScope, gid)
                    return Ast.VariableExpression(info.globalScope, gid)
                elseif isVarRef(n.base, valuesParam.scope, valuesParam.id) then
                    local slot = isSlotIndex(n.index)
                    if slot and capList[slot] then
                        local capVar = capList[slot]
                        data.scope:addReferenceToHigherScope(capVar.scope, capVar.id)
                        return Ast.IndexExpression(Ast.VariableExpression(capVar.scope, capVar.id), Ast.NumberExpression(1))
                    end
                end
            elseif n.kind == AstKind.AssignmentIndexing then
                if isVarRef(n.base, envParam.scope, envParam.id) and n.index.kind == AstKind.StringExpression then
                    local _, gid = info.globalScope:resolve(n.index.value)
                    data.scope:addReferenceToHigherScope(info.globalScope, gid)
                    return Ast.AssignmentVariable(info.globalScope, gid)
                elseif isVarRef(n.base, valuesParam.scope, valuesParam.id) then
                    local slot = isSlotIndex(n.index)
                    if slot and capList[slot] then
                        local capVar = capList[slot]
                        data.scope:addReferenceToHigherScope(capVar.scope, capVar.id)
                        return Ast.AssignmentIndexing(Ast.VariableExpression(capVar.scope, capVar.id), Ast.NumberExpression(1))
                    end
                end
            elseif isVarRef(n, envParam.scope, envParam.id) and n.kind == AstKind.VariableExpression then
                local _, gid = info.globalScope:resolve("_ENV")
                data.scope:addReferenceToHigherScope(info.globalScope, gid)
                return Ast.VariableExpression(info.globalScope, gid)
            end
        end)

        local unwrapped = dummyTop.body.statements[1].args[1]
        rebindScopesInSubtree(unwrapped, currentScope, info.globalScope)
        return unwrapped
    end

    liftClosure = function(entryBlockId, isTopLevel, isVararg, parentUpvals, enclosingScope)
        local entryIdx = leafForId(entryBlockId)
        if not entryIdx then return nil end

        local funcNodes = {}
        local funcNodeSet = {}
        local q = { entryIdx }
        funcNodeSet[entryIdx] = true
        local qh = 1
        while qh <= #q do
            local u = q[qh]
            qh = qh + 1
            funcNodes[#funcNodes + 1] = u
            local nb = getNormBlock(u)
            if nb.term.kind == "goto" and nb.term.target and not funcNodeSet[nb.term.target] then
                funcNodeSet[nb.term.target] = true
                q[#q + 1] = nb.term.target
            elseif nb.term.kind == "branch" then
                if nb.term.trueTarget and not funcNodeSet[nb.term.trueTarget] then
                    funcNodeSet[nb.term.trueTarget] = true
                    q[#q + 1] = nb.term.trueTarget
                end
                if nb.term.falseTarget and not funcNodeSet[nb.term.falseTarget] then
                    funcNodeSet[nb.term.falseTarget] = true
                    q[#q + 1] = nb.term.falseTarget
                end
            end
        end

        local funcScope = Scope:new(enclosingScope)

        local entryNb = getNormBlock(entryIdx)
        local varargRegKey = nil
        local maxArgIndex = 0
        local varargStartIdx = nil

        local entryNums = {}
        local function evalEntryNum(e)
            if not e then return nil end
            if e.kind == AstKind.NumberExpression then return e.value end
            local erk = regKeyOfNode(e, info)
            if erk and entryNums[erk] ~= nil then return entryNums[erk] end
            return nil
        end

        for _, s in ipairs(entryNb.rawStmts) do
            if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1 then
                local lk = regKeyOfNode(s.lhs[1], info)
                local rhs = s.rhs[1]
                if lk then
                    if rhs.kind == AstKind.NumberExpression then
                        entryNums[lk] = rhs.value
                    else
                        local rrk = regKeyOfNode(rhs, info)
                        entryNums[lk] = rrk and entryNums[rrk] or nil
                    end
                end
                if isTopLevel and lk and isVarRef(rhs, info.containerScope, info.argsVar) then
                    varargRegKey = lk
                elseif not isTopLevel then
                    if lk and rhs.kind == AstKind.FunctionCallExpression
                        and rhs.base.kind == AstKind.VariableExpression and rhs.base.scope == info.cffScope
                        and ((info.cffAliases[rhs.base.id] or rhs.base.id) == (info.cffAliases[info.packVar] or info.packVar))
                        and #rhs.args == 1 and rhs.args[1].kind == AstKind.FunctionCallExpression
                        and rhs.args[1].base.kind == AstKind.VariableExpression and rhs.args[1].base.scope == info.cffScope
                        and ((info.cffAliases[rhs.args[1].base.id] or rhs.args[1].base.id) == (info.cffAliases[info.selectVar] or info.selectVar))
                        and #rhs.args[1].args >= 1 then
                        local sIdx = evalEntryNum(rhs.args[1].args[1])
                        if sIdx then
                            varargRegKey = lk
                            varargStartIdx = sIdx
                        end
                    end
                end
            end
            if not isTopLevel then
                visitSub(s, function(n)
                    if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                    if n.kind == AstKind.IndexExpression
                        and isVarRef(n.base, info.containerScope, info.argsVar) then
                        local aIdx = evalEntryNum(n.index)
                        if aIdx and aIdx > maxArgIndex then maxArgIndex = aIdx end
                    end
                end, nil, info.globalScope)
            end
        end
        if not isTopLevel then
            for _, bIdx in ipairs(funcNodes) do
                if bIdx ~= entryIdx then
                    local nb = getNormBlock(bIdx)
                    for _, s in ipairs(nb.rawStmts) do
                        visitSub(s, function(n)
                            if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                            if n.kind == AstKind.IndexExpression
                                and isVarRef(n.base, info.containerScope, info.argsVar)
                                and n.index.kind == AstKind.NumberExpression then
                                if n.index.value > maxArgIndex then maxArgIndex = n.index.value end
                            end
                        end, nil, info.globalScope)
                    end
                end
            end
        end

        local fixedParamCount = 0
        if not isTopLevel then
            if isVararg and varargStartIdx then
                fixedParamCount = varargStartIdx - 1
            else
                fixedParamCount = maxArgIndex
            end
        end

        local paramIds = {}
        local fnArgs = {}
        for i = 1, fixedParamCount do
            local pid = funcScope:addVariable()
            paramIds[i] = pid
            fnArgs[#fnArgs + 1] = Ast.VariableExpression(funcScope, pid)
        end
        if not isTopLevel and isVararg then
            fnArgs[#fnArgs + 1] = Ast.VarargExpression()
        end

        local varargIndexMax = 0
        local varargDirectReads = 0
        if varargRegKey then
            for _, bIdx in ipairs(funcNodes) do
                local nb = getNormBlock(bIdx)
                local function scanVarargUse(root)
                    visitSub(root, function(n)
                        if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                        if n.kind == AstKind.FunctionCallExpression
                            and isVarRef(n.base, info.cffScope, info.unpackPackedVar)
                            and #n.args == 1 and regKeyOfNode(n.args[1], info) == varargRegKey then
                            return nil, true
                        end
                        if n.kind == AstKind.IndexExpression and regKeyOfNode(n.base, info) == varargRegKey then
                            if n.index.kind == AstKind.NumberExpression then
                                if n.index.value > varargIndexMax then varargIndexMax = n.index.value end
                            else
                                varargDirectReads = varargDirectReads + 1
                            end
                            return nil, true
                        end
                        if regKeyOfNode(n, info) == varargRegKey then
                            varargDirectReads = varargDirectReads + 1
                        end
                    end, nil, info.globalScope)
                end
                for idxS, s in ipairs(nb.rawStmts) do
                    local isInit = (bIdx == entryIdx and idxS <= (fixedParamCount * 2 + 2)
                        and s.kind == AstKind.AssignmentStatement and #s.lhs == 1
                        and regKeyOfNode(s.lhs[1], info) == varargRegKey)
                    if not isInit then scanVarargUse(s) end
                end
                if nb.term.kind == "branch" then scanVarargUse(nb.term.cond) end
            end
        end

        local varargTableVarId = nil
        if varargRegKey and (varargIndexMax >= 2 or varargDirectReads > 0) then
            varargTableVarId = funcScope:addVariable()
        end

        local upwardExposed = {}
        local everRead = {}
        local everWritten = {}
        for _, bIdx in ipairs(funcNodes) do
            local nb = getNormBlock(bIdx)
            local writtenInBlock = {}
            local function noteReads(expr)
                visitSub(expr, function(n)
                    if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                    local rk = regKeyOfNode(n, info)
                    if rk and rk ~= varargRegKey and n.kind ~= AstKind.AssignmentVariable and n.kind ~= AstKind.AssignmentIndexing then
                        everRead[rk] = true
                        if not writtenInBlock[rk] then
                            upwardExposed[rk] = true
                        end
                    end
                end, nil, info.globalScope)
            end
            if nb.term.kind == "branch" and nb.term.condPos == 0 then
                noteReads(nb.term.cond)
            end
            for idxS, s in ipairs(nb.rawStmts) do
                if s.kind == AstKind.AssignmentStatement then
                    for _, l in ipairs(s.lhs) do
                        if l.kind == AstKind.AssignmentIndexing and not regKeyOfNode(l, info) then
                            noteReads(l.base)
                            noteReads(l.index)
                        end
                    end
                    for _, r in ipairs(s.rhs) do noteReads(r) end
                    for _, l in ipairs(s.lhs) do
                        local rk = regKeyOfNode(l, info)
                        if rk and rk ~= varargRegKey then
                            writtenInBlock[rk] = true
                            everWritten[rk] = true
                        end
                    end
                elseif COMPOUND_CONSTRUCTORS[s.kind] then
                    local rk = regKeyOfNode(s.lhs, info)
                    if rk then
                        everRead[rk] = true
                        if not writtenInBlock[rk] then upwardExposed[rk] = true end
                    else
                        noteReads(s.lhs.base)
                        noteReads(s.lhs.index)
                    end
                    noteReads(s.rhs)
                    if rk then
                        writtenInBlock[rk] = true
                        everWritten[rk] = true
                    end
                elseif s.kind == AstKind.IfStatement then
                    noteReads(s)
                    visitSub(s, function(n)
                        if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                        if n.kind == AstKind.AssignmentStatement then
                            for _, l in ipairs(n.lhs) do
                                local rk = regKeyOfNode(l, info)
                                if rk and rk ~= varargRegKey then
                                    everWritten[rk] = true
                                    upwardExposed[rk] = true
                                end
                            end
                        end
                    end, nil, info.globalScope)
                else
                    noteReads(s)
                end
                if nb.term.kind == "branch" and nb.term.condPos == idxS then
                    noteReads(nb.term.cond)
                end
            end
            if nb.term.kind == "branch" and (not nb.term.condPos or nb.term.condPos > #nb.rawStmts) then
                noteReads(nb.term.cond)
            end
        end

        local uniqueConstNumByReg = {}
        do
            local poisoned = {}
            for _, bIdx in ipairs(funcNodes) do
                local nb = getNormBlock(bIdx)
                for _, s in ipairs(nb.rawStmts) do
                    visitSub(s, function(n)
                        if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                        if n.kind == AstKind.AssignmentStatement then
                            for i = 1, #n.lhs do
                                local rk = regKeyOfNode(n.lhs[i], info)
                                local r = n.rhs[i]
                                if rk then
                                    if r and r.kind == AstKind.NumberExpression then
                                        if not poisoned[rk] then
                                            if uniqueConstNumByReg[rk] == nil or uniqueConstNumByReg[rk] == r.value then
                                                uniqueConstNumByReg[rk] = r.value
                                            else
                                                uniqueConstNumByReg[rk] = nil
                                                poisoned[rk] = true
                                            end
                                        end
                                    elseif not (r and r.kind == AstKind.NilExpression) then
                                        uniqueConstNumByReg[rk] = nil
                                        poisoned[rk] = true
                                    end
                                end
                            end
                        elseif COMPOUND_CONSTRUCTORS[n.kind] then
                            local rk = regKeyOfNode(n.lhs, info)
                            if rk then
                                uniqueConstNumByReg[rk] = nil
                                poisoned[rk] = true
                            end
                        end
                    end, nil, info.globalScope)
                end
            end
        end

        local regBinding = {}
        local regOrder = {}
        for rk in pairs(everWritten) do
            if everRead[rk] then
                regOrder[#regOrder + 1] = rk
            end
        end
        for rk in pairs(everRead) do
            if not everWritten[rk] then
                regOrder[#regOrder + 1] = rk
            end
        end
        table.sort(regOrder)

        local localSpillId = nil
        local scalarCount = 0
        local function ensureRegBinding(rk)
            if regBinding[rk] then return regBinding[rk] end
            if not upwardExposed[rk] or scalarCount < 150 then
                if upwardExposed[rk] then
                    scalarCount = scalarCount + 1
                end
                local vid = funcScope:addVariable()
                regBinding[rk] = { kind = "local", id = vid }
            else
                if not localSpillId then localSpillId = funcScope:addVariable() end
                scalarCount = scalarCount + 1
                regBinding[rk] = { kind = "spill", idx = scalarCount - 150 }
            end
            return regBinding[rk]
        end

        for _, rk in ipairs(regOrder) do
            if upwardExposed[rk] then
                ensureRegBinding(rk)
            end
        end

        local function makeRegExpr(rk, curScope)
            local b = ensureRegBinding(rk)
            if b.kind == "local" then
                curScope:addReferenceToHigherScope(funcScope, b.id)
                return Ast.VariableExpression(funcScope, b.id)
            else
                curScope:addReferenceToHigherScope(funcScope, localSpillId)
                return Ast.IndexExpression(Ast.VariableExpression(funcScope, localSpillId), Ast.NumberExpression(b.idx))
            end
        end

        local function makeRegLhs(rk, curScope)
            local b = ensureRegBinding(rk)
            if b.kind == "local" then
                curScope:addReferenceToHigherScope(funcScope, b.id)
                return Ast.AssignmentVariable(funcScope, b.id)
            else
                curScope:addReferenceToHigherScope(funcScope, localSpillId)
                return Ast.AssignmentIndexing(Ast.VariableExpression(funcScope, localSpillId), Ast.NumberExpression(b.idx))
            end
        end

        local syntheticInlineIds = {}
        local liftedBlocks = {}

        for _, bIdx in ipairs(funcNodes) do
            local nb = getNormBlock(bIdx)
            local curStmts = {}
            local blockReturnArgs = nil
            local liftedBranchCond = nil
            local packedInBlock = {}
            local constStrInReg = {}

            local function emitPreStmt(s)
                curStmts[#curStmts + 1] = s
            end

            local function snapshotExprListAtNow(exprList)
                local snapMap = {}
                for pIdx = 1, #exprList do
                    local wrapTop = Ast.TopNode(Ast.Block({ Ast.ReturnStatement({ exprList[pIdx] }) }, funcScope), info.globalScope)
                    visitast(wrapTop, function(n)
                        if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                    end, function(n)
                        if n.kind == AstKind.VariableExpression and n.scope == funcScope then
                            local sid = snapMap[n.id]
                            if not sid then
                                sid = funcScope:addVariable()
                                snapMap[n.id] = sid
                                syntheticInlineIds[sid] = true
                                funcScope:addReferenceToHigherScope(funcScope, n.id)
                                funcScope:addReferenceToHigherScope(funcScope, sid)
                                curStmts[#curStmts + 1] = Ast.AssignmentStatement(
                                    { Ast.AssignmentVariable(funcScope, sid) },
                                    { Ast.VariableExpression(funcScope, n.id) }
                                )
                            end
                            funcScope:addReferenceToHigherScope(funcScope, sid)
                            return Ast.VariableExpression(funcScope, sid)
                        end
                    end)
                    exprList[pIdx] = wrapTop.body.statements[1].args[1]
                end
                return exprList
            end

            local constNumInReg = {}
            local upvalAliasInReg = {}
            local tableInReg = {}

            local function evalCapTable(tExpr)
                if not tExpr then return nil end
                if tExpr.kind == AstKind.TableConstructorExpression then
                    return tExpr
                end
                local trk = regKeyOfNode(tExpr, info)
                if trk and tableInReg[trk] then
                    return tableInReg[trk]
                end
                return nil
            end

            local function evalIndexNum(idxExpr)
                if not idxExpr then return nil end
                if idxExpr.kind == AstKind.NumberExpression then
                    return idxExpr.value
                end
                local irk = regKeyOfNode(idxExpr, info)
                if irk then
                    if constNumInReg[irk] ~= nil then
                        return constNumInReg[irk]
                    end
                    if uniqueConstNumByReg and uniqueConstNumByReg[irk] ~= nil then
                        return uniqueConstNumByReg[irk]
                    end
                end
                return nil
            end

            local function resolveCaptureEntry(capExpr)
                if capExpr.kind == AstKind.FunctionCallExpression
                    and isVarRef(capExpr.base, info.cffScope, info.allocUpvalFunction) then
                    local cid = funcScope:addVariable()
                    emitPreStmt(Ast.LocalVariableDeclaration(funcScope, { cid }, { Ast.TableConstructorExpression({}) }))
                    return { scope = funcScope, id = cid }
                elseif capExpr.kind == AstKind.IndexExpression
                    and isVarRef(capExpr.base, info.containerScope, info.currentUpvaluesVar) then
                    local u = evalIndexNum(capExpr.index)
                    if u then
                        return parentUpvals[u]
                    end
                else
                    local rk = regKeyOfNode(capExpr, info)
                    if rk then
                        if upvalAliasInReg[rk] then
                            return upvalAliasInReg[rk]
                        end
                        local snapId = funcScope:addVariable()
                        emitPreStmt(Ast.LocalVariableDeclaration(funcScope, { snapId }, { makeRegExpr(rk, funcScope) }))
                        return { scope = funcScope, id = snapId }
                    end
                end
                local fallbackId = funcScope:addVariable()
                emitPreStmt(Ast.LocalVariableDeclaration(funcScope, { fallbackId }, { Ast.TableConstructorExpression({}) }))
                return { scope = funcScope, id = fallbackId }
            end

            local rewriteExpr
            local aliasInReg = {}
            local leafLocalIds = {}

            local function derefCffVar(node)
                if not node then return nil end
                local rk = regKeyOfNode(node, info)
                if rk and aliasInReg[rk] then
                    node = aliasInReg[rk]
                end
                if node.kind == AstKind.VariableExpression and node.scope == info.cffScope
                    and info.cffAliases and info.cffAliases[node.id] then
                    return Ast.VariableExpression(info.cffScope, info.cffAliases[node.id])
                end
                return node
            end

            local function isEnvNode(node)
                local d = derefCffVar(node)
                if not d then return false end
                if isVarRef(d, info.containerScope, info.currentEnvVar) then return true end
                if info.envVar and isVarRef(d, info.cffScope, info.envVar) then return true end
                return false
            end

            local function isCffHelper(node, helperId)
                if not helperId then return false end
                local d = derefCffVar(node)
                if not d or d.scope ~= info.cffScope then return false end
                local canonHelper = (info.cffAliases and info.cffAliases[helperId]) or helperId
                local canonNode = (info.cffAliases and info.cffAliases[d.id]) or d.id
                return canonNode == canonHelper
            end

            resolveCaptureEntry = function(capExpr)
                if capExpr.kind == AstKind.FunctionCallExpression
                    and isCffHelper(capExpr.base, info.allocUpvalFunction) then
                    local cid = funcScope:addVariable()
                    emitPreStmt(Ast.LocalVariableDeclaration(funcScope, { cid }, { Ast.TableConstructorExpression({}) }))
                    return { scope = funcScope, id = cid }
                elseif capExpr.kind == AstKind.IndexExpression
                    and isVarRef(capExpr.base, info.containerScope, info.currentUpvaluesVar) then
                    local u = evalIndexNum(capExpr.index)
                    if u then
                        return parentUpvals[u]
                    end
                else
                    local rk = regKeyOfNode(capExpr, info)
                    if rk then
                        if upvalAliasInReg[rk] then
                            return upvalAliasInReg[rk]
                        end
                        local snapId = funcScope:addVariable()
                        emitPreStmt(Ast.LocalVariableDeclaration(funcScope, { snapId }, { makeRegExpr(rk, funcScope) }))
                        return { scope = funcScope, id = snapId }
                    end
                end
                local fallbackId = funcScope:addVariable()
                emitPreStmt(Ast.LocalVariableDeclaration(funcScope, { fallbackId }, { Ast.TableConstructorExpression({}) }))
                return { scope = funcScope, id = fallbackId }
            end

            local function packedKeyOfNode(node)
                local rk = regKeyOfNode(node, info)
                if rk then return rk end
                if node and node.kind == AstKind.VariableExpression and not node.scope.isGlobal then
                    local lid = leafLocalIds[tostring(node.scope) .. ":" .. tostring(node.id)]
                    if lid then return "ll_" .. tostring(lid) end
                end
                return nil
            end

            local function rewriteArgList(rawArgs)
                local out = {}
                for i = 1, #rawArgs do
                    local a = rawArgs[i]
                    if i == #rawArgs and a.kind == AstKind.FunctionCallExpression
                        and isCffHelper(a.base, info.unpackPackedVar) and #a.args == 1 then
                        local inner = a.args[1]
                        local irk = packedKeyOfNode(inner)
                        if irk and irk == varargRegKey then
                            out[#out + 1] = Ast.VarargExpression()
                        elseif irk and packedInBlock[irk] then
                            local pk = packedInBlock[irk]
                            packedInBlock[irk] = nil
                            for _, pe in ipairs(pk.exprs) do
                                out[#out + 1] = pe
                            end
                        else
                            local tblExpr = rewriteExpr(inner)
                            local upkId = getHelperVar("unpack")
                            funcScope:addReferenceToHigherScope(holderScope, upkId)
                            out[#out + 1] = Ast.FunctionCallExpression(
                                Ast.VariableExpression(holderScope, upkId),
                                { tblExpr }
                            )
                        end
                    else
                        out[#out + 1] = rewriteExpr(a)
                    end
                end
                return out
            end

            rewriteExpr = function(expr)
                if not expr then return Ast.NilExpression() end
                if isEnvNode(expr) then
                    local _, gid = info.globalScope:resolve("_G")
                    funcScope:addReferenceToHigherScope(info.globalScope, gid)
                    return Ast.VariableExpression(info.globalScope, gid)
                end
                local rk = regKeyOfNode(expr, info)
                if rk then
                    if rk == varargRegKey then
                        if varargTableVarId then
                            funcScope:addReferenceToHigherScope(funcScope, varargTableVarId)
                            return Ast.VariableExpression(funcScope, varargTableVarId)
                        end
                        local ve = Ast.VarargExpression()
                        ve.isParenthesizedExpression = true
                        return ve
                    end
                    if aliasInReg[rk] then
                        local av = aliasInReg[rk]
                        funcScope:addReferenceToHigherScope(av.scope, av.id)
                        return Ast.VariableExpression(av.scope, av.id)
                    end
                    return makeRegExpr(rk, funcScope)
                end

                local k = expr.kind
                if k == AstKind.NumberExpression or k == AstKind.StringExpression
                    or k == AstKind.BooleanExpression or k == AstKind.NilExpression
                    or k == AstKind.VarargExpression then
                    local cp
                    if k == AstKind.NumberExpression then cp = Ast.NumberExpression(expr.value)
                    elseif k == AstKind.StringExpression then cp = Ast.StringExpression(expr.value)
                    elseif k == AstKind.BooleanExpression then cp = Ast.BooleanExpression(expr.value)
                    elseif k == AstKind.NilExpression then cp = Ast.NilExpression()
                    else cp = Ast.VarargExpression() end
                    if expr.isParenthesizedExpression then cp.isParenthesizedExpression = true end
                    return cp
                end

                if k == AstKind.IndexExpression then
                    if isVarRef(expr.base, info.containerScope, info.currentUpvaluesVar) then
                        local u = evalIndexNum(expr.index)
                        local uv = u and parentUpvals[u] or nil
                        if uv then
                            funcScope:addReferenceToHigherScope(uv.scope, uv.id)
                            return Ast.VariableExpression(uv.scope, uv.id)
                        end
                    end
                    if isVarRef(expr.base, info.containerScope, info.argsVar) then
                        local idx = evalIndexNum(expr.index)
                        if idx then
                            if paramIds[idx] then
                                funcScope:addReferenceToHigherScope(funcScope, paramIds[idx])
                                return Ast.VariableExpression(funcScope, paramIds[idx])
                            end
                            return Ast.NilExpression()
                        end
                    end
                    if varargRegKey and regKeyOfNode(expr.base, info) == varargRegKey then
                        local idx = evalIndexNum(expr.index)
                        if idx then
                            if idx == 1 and not varargTableVarId then
                                local ve = Ast.VarargExpression()
                                ve.isParenthesizedExpression = true
                                return ve
                            elseif varargTableVarId then
                                funcScope:addReferenceToHigherScope(funcScope, varargTableVarId)
                                return Ast.IndexExpression(
                                    Ast.VariableExpression(funcScope, varargTableVarId),
                                    Ast.NumberExpression(idx)
                                )
                            end
                        end
                    end
                    if isEnvNode(expr.base) then
                        local idxRk = regKeyOfNode(expr.index, info)
                        if idxRk and constStrInReg[idxRk] ~= nil then
                            local _, gid = info.globalScope:resolve(constStrInReg[idxRk])
                            funcScope:addReferenceToHigherScope(info.globalScope, gid)
                            return Ast.VariableExpression(info.globalScope, gid)
                        end
                        local idx = rewriteExpr(expr.index)
                        if idx.kind == AstKind.StringExpression then
                            local _, gid = info.globalScope:resolve(idx.value)
                            funcScope:addReferenceToHigherScope(info.globalScope, gid)
                            return Ast.VariableExpression(info.globalScope, gid)
                        end
                        local _, gid = info.globalScope:resolve("_G")
                        funcScope:addReferenceToHigherScope(info.globalScope, gid)
                        return Ast.IndexExpression(Ast.VariableExpression(info.globalScope, gid), idx)
                    end
                    if isCffHelper(expr.base, info.upvaluesTable) then
                        if expr.index.kind == AstKind.IndexExpression
                            and isVarRef(expr.index.base, info.containerScope, info.currentUpvaluesVar) then
                            local u = evalIndexNum(expr.index.index)
                            local uv = u and parentUpvals[u] or nil
                            if uv then
                                funcScope:addReferenceToHigherScope(uv.scope, uv.id)
                                return Ast.IndexExpression(Ast.VariableExpression(uv.scope, uv.id), Ast.NumberExpression(1))
                            end
                        end
                        return Ast.IndexExpression(rewriteExpr(expr.index), Ast.NumberExpression(1))
                    end
                    return Ast.IndexExpression(rewriteExpr(expr.base), rewriteExpr(expr.index))
                end

                if k == AstKind.FunctionCallExpression then
                    if isCffHelper(expr.base, info.allocUpvalFunction) then
                        return Ast.TableConstructorExpression({})
                    end
                    if isCffHelper(expr.base, info.freeUpvalueFunc) then
                        return Ast.NilExpression()
                    end
                    if isCffHelper(expr.base, info.callFunctionVar) and #expr.args >= 2 then
                        local fnExpr = rewriteExpr(expr.args[1])
                        local rawCallArgs = {}
                        for i = 3, #expr.args do rawCallArgs[#rawCallArgs + 1] = expr.args[i] end
                        return Ast.FunctionCallExpression(fnExpr, rewriteArgList(rawCallArgs))
                    end
                    if isCffHelper(expr.base, info.createVarargClosureVar)
                        and #expr.args >= 2 then
                        local cEntry = evalIndexNum(expr.args[1])
                        local cTbl = evalCapTable(expr.args[2])
                        if cEntry and cTbl then
                            local childCaps = {}
                            for i, ent in ipairs(cTbl.entries) do
                                childCaps[i] = resolveCaptureEntry(ent.value)
                            end
                            return liftClosure(cEntry, false, true, childCaps, funcScope)
                        end
                    end
                    local dBase = derefCffVar(expr.base)
                    if dBase and dBase.kind == AstKind.VariableExpression and dBase.scope == info.cffScope
                        and info.createClosureArity[dBase.id] ~= nil
                        and #expr.args >= 2 then
                        local cEntry = evalIndexNum(expr.args[1])
                        local cTbl = evalCapTable(expr.args[2])
                        if cEntry and cTbl then
                            local childCaps = {}
                            for i, ent in ipairs(cTbl.entries) do
                                childCaps[i] = resolveCaptureEntry(ent.value)
                            end
                            return liftClosure(cEntry, false, false, childCaps, funcScope)
                        end
                    end
                    if expr.base.kind == AstKind.FunctionLiteralExpression and #expr.args == 3
                        and isEnvNode(expr.args[2])
                        and isCffHelper(expr.args[3], info.upvaluesTable) then
                        local unwrapped = unwrapNativeCall(expr.base, expr.args[1], resolveCaptureEntry, funcScope)
                        if unwrapped then return unwrapped end
                    end
                    if isCffHelper(expr.base, info.tonumberVar) then
                        local tnId = getHelperVar("tonumber")
                        funcScope:addReferenceToHigherScope(holderScope, tnId)
                        return Ast.FunctionCallExpression(Ast.VariableExpression(holderScope, tnId), rewriteArgList(expr.args))
                    end
                    if isCffHelper(expr.base, info.errorVar) then
                        local erId = getHelperVar("error")
                        funcScope:addReferenceToHigherScope(holderScope, erId)
                        return Ast.FunctionCallExpression(Ast.VariableExpression(holderScope, erId), rewriteArgList(expr.args))
                    end
                    if isCffHelper(expr.base, info.selectVar) then
                        local slId = getHelperVar("select")
                        funcScope:addReferenceToHigherScope(holderScope, slId)
                        return Ast.FunctionCallExpression(Ast.VariableExpression(holderScope, slId), rewriteArgList(expr.args))
                    end
                    if isCffHelper(expr.base, info.packVar) then
                        local vals = rewriteArgList(expr.args)
                        local pkId = getHelperVar("pack")
                        funcScope:addReferenceToHigherScope(holderScope, pkId)
                        return Ast.FunctionCallExpression(Ast.VariableExpression(holderScope, pkId), vals)
                    end
                    return Ast.FunctionCallExpression(rewriteExpr(expr.base), rewriteArgList(expr.args))
                end

                if k == AstKind.PassSelfFunctionCallExpression then
                    return Ast.PassSelfFunctionCallExpression(rewriteExpr(expr.base), expr.passSelfFunctionName, rewriteArgList(expr.args))
                end

                if k == AstKind.TableConstructorExpression then
                    local entries = {}
                    for idxE, ent in ipairs(expr.entries) do
                        if ent.kind == AstKind.TableEntry then
                            if idxE == #expr.entries and ent.value.kind == AstKind.FunctionCallExpression
                                and isCffHelper(ent.value.base, info.unpackPackedVar) then
                                local tail = rewriteArgList({ ent.value })
                                for _, te in ipairs(tail) do entries[#entries + 1] = Ast.TableEntry(te) end
                            else
                                entries[#entries + 1] = Ast.TableEntry(rewriteExpr(ent.value))
                            end
                        else
                            entries[#entries + 1] = Ast.KeyedTableEntry(rewriteExpr(ent.key), rewriteExpr(ent.value))
                        end
                    end
                    return Ast.TableConstructorExpression(entries)
                end

                if BIN_CONSTRUCTORS[k] then
                    local res = BIN_CONSTRUCTORS[k](rewriteExpr(expr.lhs), rewriteExpr(expr.rhs))
                    if expr.isParenthesizedExpression then res.isParenthesizedExpression = true end
                    return res
                end

                if UNARY_CONSTRUCTORS[k] then
                    local res = UNARY_CONSTRUCTORS[k](rewriteExpr(expr.rhs))
                    if expr.isParenthesizedExpression then res.isParenthesizedExpression = true end
                    return res
                end

                if k == AstKind.IfElseExpression then
                    local eifs = {}
                    for _, eif in ipairs(expr.elseifs) do
                        eifs[#eifs + 1] = { condition = rewriteExpr(eif.condition), value = rewriteExpr(eif.value) }
                    end
                    return Ast.IfElseExpression(rewriteExpr(expr.condition), rewriteExpr(expr.true_value), eifs, rewriteExpr(expr.false_value))
                end

                if k == AstKind.VariableExpression then
                    if isEnvNode(expr) then
                        local _, gid = info.globalScope:resolve("_G")
                        funcScope:addReferenceToHigherScope(info.globalScope, gid)
                        return Ast.VariableExpression(info.globalScope, gid)
                    end
                    if not expr.scope.isGlobal then
                        local lid = leafLocalIds[tostring(expr.scope) .. ":" .. tostring(expr.id)]
                        if lid then
                            funcScope:addReferenceToHigherScope(funcScope, lid)
                            return Ast.VariableExpression(funcScope, lid)
                        end
                        funcScope:addReferenceToHigherScope(expr.scope, expr.id)
                    else
                        funcScope:addReferenceToHigherScope(info.globalScope, expr.id)
                    end
                    return Ast.VariableExpression(expr.scope, expr.id)
                end

                return expr
            end

            local function rewriteLhs(lhs)
                local rk = regKeyOfNode(lhs, info)
                if rk then
                    return makeRegLhs(rk, funcScope)
                end
                if lhs.kind == AstKind.AssignmentIndexing then
                    if isEnvNode(lhs.base) then
                        local idxRk = regKeyOfNode(lhs.index, info)
                        if idxRk and constStrInReg[idxRk] ~= nil then
                            local _, gid = info.globalScope:resolve(constStrInReg[idxRk])
                            funcScope:addReferenceToHigherScope(info.globalScope, gid)
                            return Ast.AssignmentVariable(info.globalScope, gid)
                        end
                        local idx = rewriteExpr(lhs.index)
                        if idx.kind == AstKind.StringExpression then
                            local _, gid = info.globalScope:resolve(idx.value)
                            funcScope:addReferenceToHigherScope(info.globalScope, gid)
                            return Ast.AssignmentVariable(info.globalScope, gid)
                        end
                        local _, gid = info.globalScope:resolve("_G")
                        funcScope:addReferenceToHigherScope(info.globalScope, gid)
                        return Ast.AssignmentIndexing(Ast.VariableExpression(info.globalScope, gid), idx)
                    end
                    if isCffHelper(lhs.base, info.upvaluesTable) then
                        if lhs.index.kind == AstKind.IndexExpression
                            and isVarRef(lhs.index.base, info.containerScope, info.currentUpvaluesVar) then
                            local u = evalIndexNum(lhs.index.index)
                            local uv = u and parentUpvals[u] or nil
                            if uv then
                                funcScope:addReferenceToHigherScope(uv.scope, uv.id)
                                return Ast.AssignmentIndexing(Ast.VariableExpression(uv.scope, uv.id), Ast.NumberExpression(1))
                            end
                        end
                        return Ast.AssignmentIndexing(rewriteExpr(lhs.index), Ast.NumberExpression(1))
                    end
                    return Ast.AssignmentIndexing(rewriteExpr(lhs.base), rewriteExpr(lhs.index))
                end
                if lhs.kind == AstKind.AssignmentVariable then
                    local lid = leafLocalIds[tostring(lhs.scope) .. ":" .. tostring(lhs.id)]
                    if lid then
                        funcScope:addReferenceToHigherScope(funcScope, lid)
                        return Ast.AssignmentVariable(funcScope, lid)
                    end
                    funcScope:addReferenceToHigherScope(lhs.scope, lhs.id)
                    return Ast.AssignmentVariable(lhs.scope, lhs.id)
                end
                return lhs
            end

            local rawList = nb.rawStmts
            if nb.term.kind == "branch" and nb.term.condPos == 0 then
                liftedBranchCond = snapshotExprListAtNow({ rewriteExpr(nb.term.cond) })[1]
            end
            for idxS = 1, #rawList do
                local s = rawList[idxS]
                if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1 then
                    local lhs, rhs = s.lhs[1], s.rhs[1]
                    local lk = regKeyOfNode(lhs, info)
                    local rhsCffTarget = nil
                    if rhs.kind == AstKind.VariableExpression then
                        local dRhs = derefCffVar(rhs)
                        if dRhs and (dRhs.scope == info.cffScope or isVarRef(dRhs, info.containerScope, info.currentEnvVar)) then
                            rhsCffTarget = dRhs
                        end
                    end
                    if isVarRef(lhs, info.containerScope, info.returnVar) then
                        if rhs.kind == AstKind.FunctionCallExpression
                            and isCffHelper(rhs.base, info.packVar) then
                            blockReturnArgs = snapshotExprListAtNow(rewriteArgList(rhs.args))
                        else
                            blockReturnArgs = snapshotExprListAtNow({ rewriteExpr(rhs) })
                        end
                    elseif lk and rhsCffTarget then
                        constStrInReg[lk] = nil
                        constNumInReg[lk] = nil
                        packedInBlock[lk] = nil
                        aliasInReg[lk] = rhsCffTarget
                    elseif lk and lk == varargRegKey and bIdx == entryIdx then
                        constStrInReg[lk] = nil
                        constNumInReg[lk] = nil
                        aliasInReg[lk] = nil
                        if varargTableVarId then
                            funcScope:addReferenceToHigherScope(funcScope, varargTableVarId)
                            curStmts[#curStmts + 1] = Ast.AssignmentStatement(
                                { Ast.AssignmentVariable(funcScope, varargTableVarId) },
                                { Ast.TableConstructorExpression({ Ast.TableEntry(Ast.VarargExpression()) }) }
                            )
                        end
                    elseif lk and rhs.kind == AstKind.FunctionCallExpression
                        and isCffHelper(rhs.base, info.packVar)
                        and not upwardExposed[lk] then
                        constStrInReg[lk] = nil
                        constNumInReg[lk] = nil
                        aliasInReg[lk] = nil
                        local packedExprs = snapshotExprListAtNow(rewriteArgList(rhs.args))
                        if #rhs.args == 1 and rhs.args[1].kind ~= AstKind.FunctionCallExpression
                            and rhs.args[1].kind ~= AstKind.PassSelfFunctionCallExpression
                            and rhs.args[1].kind ~= AstKind.VarargExpression
                            and #packedExprs == 1 then
                            packedExprs[1].isParenthesizedExpression = true
                        end
                        packedInBlock[lk] = { exprs = packedExprs }
                    elseif lk and rhs.kind == AstKind.NilExpression and packedInBlock[lk] then
                        constStrInReg[lk] = nil
                        constNumInReg[lk] = nil
                        aliasInReg[lk] = nil
                        packedInBlock[lk] = nil
                    elseif lk and not everRead[lk] then
                        local rhsRk = regKeyOfNode(rhs, info)
                        aliasInReg[lk] = rhsRk and aliasInReg[rhsRk] or nil
                        if rhs.kind == AstKind.IndexExpression
                            and isVarRef(rhs.base, info.containerScope, info.currentUpvaluesVar) then
                            local u = evalIndexNum(rhs.index)
                            upvalAliasInReg[lk] = u and parentUpvals[u] or nil
                        else
                            upvalAliasInReg[lk] = rhsRk and upvalAliasInReg[rhsRk] or nil
                        end
                        if rhs.kind == AstKind.StringExpression then
                            constStrInReg[lk] = rhs.value
                            constNumInReg[lk] = nil
                            tableInReg[lk] = nil
                        elseif rhs.kind == AstKind.NumberExpression then
                            constNumInReg[lk] = rhs.value
                            constStrInReg[lk] = nil
                            tableInReg[lk] = nil
                        elseif rhs.kind == AstKind.TableConstructorExpression then
                            tableInReg[lk] = rhs
                            constStrInReg[lk] = nil
                            constNumInReg[lk] = nil
                        elseif rhsRk then
                            constStrInReg[lk] = constStrInReg[rhsRk]
                            constNumInReg[lk] = constNumInReg[rhsRk]
                            tableInReg[lk] = tableInReg[rhsRk]
                        else
                            constStrInReg[lk] = nil
                            constNumInReg[lk] = nil
                            tableInReg[lk] = nil
                        end
                        local rExpr = rewriteExpr(rhs)
                        if rExpr.kind == AstKind.FunctionCallExpression then
                            curStmts[#curStmts + 1] = Ast.FunctionCallStatement(rExpr.base, rExpr.args)
                        elseif rExpr.kind == AstKind.PassSelfFunctionCallExpression then
                            curStmts[#curStmts + 1] = Ast.PassSelfFunctionCallStatement(rExpr.base, rExpr.passSelfFunctionName, rExpr.args)
                        elseif exprHasCall(rExpr, info.globalScope) then
                            local tmpId = funcScope:addVariable()
                            curStmts[#curStmts + 1] = Ast.LocalVariableDeclaration(funcScope, { tmpId }, { rExpr })
                        end
                    else
                        local rhsRk = regKeyOfNode(rhs, info)
                        local prevStr = rhsRk and constStrInReg[rhsRk] or nil
                        local prevNum = rhsRk and constNumInReg[rhsRk] or nil
                        local prevTbl = rhsRk and tableInReg[rhsRk] or nil
                        local prevAlias = rhsRk and aliasInReg[rhsRk] or nil
                        local prevUpval = nil
                        if rhs.kind == AstKind.IndexExpression
                            and isVarRef(rhs.base, info.containerScope, info.currentUpvaluesVar) then
                            local u = evalIndexNum(rhs.index)
                            prevUpval = u and parentUpvals[u] or nil
                        elseif rhsRk then
                            prevUpval = upvalAliasInReg[rhsRk]
                        end
                        if lk then
                            aliasInReg[lk] = prevAlias
                            upvalAliasInReg[lk] = prevUpval
                            if rhs.kind == AstKind.TableConstructorExpression then
                                tableInReg[lk] = rhs
                            else
                                tableInReg[lk] = prevTbl
                            end
                        end
                        local newLhs = rewriteLhs(lhs)
                        local newRhs = rewriteExpr(rhs)
                        if lk then
                            if rhs.kind == AstKind.StringExpression then
                                constStrInReg[lk] = rhs.value
                                constNumInReg[lk] = nil
                            elseif rhs.kind == AstKind.NumberExpression then
                                constNumInReg[lk] = rhs.value
                                constStrInReg[lk] = nil
                            elseif rhsRk then
                                constStrInReg[lk] = prevStr
                                constNumInReg[lk] = prevNum
                            else
                                constStrInReg[lk] = nil
                                constNumInReg[lk] = nil
                            end
                        end
                        curStmts[#curStmts + 1] = Ast.AssignmentStatement({ newLhs }, { newRhs })
                    end
                elseif s.kind == AstKind.LocalVariableDeclaration then
                    if #s.ids == 1 and s.expressions and #s.expressions == 1
                        and s.expressions[1].kind == AstKind.FunctionCallExpression
                        and isCffHelper(s.expressions[1].base, info.packVar) then
                        local lid = funcScope:addVariable()
                        leafLocalIds[tostring(s.scope) .. ":" .. tostring(s.ids[1])] = lid
                        local rhs = s.expressions[1]
                        local packedExprs = snapshotExprListAtNow(rewriteArgList(rhs.args))
                        if #rhs.args == 1 and rhs.args[1].kind ~= AstKind.FunctionCallExpression
                            and rhs.args[1].kind ~= AstKind.PassSelfFunctionCallExpression
                            and rhs.args[1].kind ~= AstKind.VarargExpression
                            and #packedExprs == 1 then
                            packedExprs[1].isParenthesizedExpression = true
                        end
                        packedInBlock["ll_" .. tostring(lid)] = { exprs = packedExprs }
                    else
                        local newIds = {}
                        local newExprs = {}
                        for i = 1, #s.ids do
                            local lid = funcScope:addVariable()
                            leafLocalIds[tostring(s.scope) .. ":" .. tostring(s.ids[i])] = lid
                            newIds[i] = lid
                        end
                        for i = 1, #(s.expressions or {}) do
                            newExprs[i] = rewriteExpr(s.expressions[i])
                        end
                        curStmts[#curStmts + 1] = Ast.LocalVariableDeclaration(funcScope, newIds, newExprs)
                    end
                elseif s.kind == AstKind.FunctionCallStatement then
                    local callExpr = rewriteExpr(Ast.FunctionCallExpression(s.base, s.args))
                    if callExpr.kind == AstKind.FunctionCallExpression then
                        curStmts[#curStmts + 1] = Ast.FunctionCallStatement(callExpr.base, callExpr.args)
                    elseif callExpr.kind == AstKind.PassSelfFunctionCallExpression then
                        curStmts[#curStmts + 1] = Ast.PassSelfFunctionCallStatement(callExpr.base, callExpr.passSelfFunctionName, callExpr.args)
                    end
                elseif s.kind == AstKind.PassSelfFunctionCallStatement then
                    curStmts[#curStmts + 1] = Ast.PassSelfFunctionCallStatement(rewriteExpr(s.base), s.passSelfFunctionName, rewriteArgList(s.args))
                elseif s.kind == AstKind.AssignmentStatement then
                    local nl, nr = {}, {}
                    for i = 1, #s.lhs do nl[i] = rewriteLhs(s.lhs[i]) end
                    for i = 1, #s.rhs do nr[i] = rewriteExpr(s.rhs[i]) end
                    for i = 1, #s.lhs do
                        local lk = regKeyOfNode(s.lhs[i], info)
                        if lk then
                            constStrInReg[lk] = nil
                            constNumInReg[lk] = nil
                            aliasInReg[lk] = nil
                        end
                    end
                    curStmts[#curStmts + 1] = Ast.AssignmentStatement(nl, nr)
                elseif COMPOUND_CONSTRUCTORS[s.kind] then
                    local lk = regKeyOfNode(s.lhs, info)
                    local nl = rewriteLhs(s.lhs)
                    local nr = rewriteExpr(s.rhs)
                    if lk then constStrInReg[lk] = nil end
                    if targetLuaVersion == LuaVersion.Lua51 then
                        local binMap = {
                            [AstKind.CompoundAddStatement] = Ast.AddExpression,
                            [AstKind.CompoundSubStatement] = Ast.SubExpression,
                            [AstKind.CompoundMulStatement] = Ast.MulExpression,
                            [AstKind.CompoundDivStatement] = Ast.DivExpression,
                            [AstKind.CompoundModStatement] = Ast.ModExpression,
                            [AstKind.CompoundPowStatement] = Ast.PowExpression,
                            [AstKind.CompoundConcatStatement] = Ast.StrCatExpression,
                        }
                        if nl.kind == AstKind.AssignmentVariable then
                            nl.scope:addReferenceToHigherScope(nl.scope, nl.id)
                            curStmts[#curStmts + 1] = Ast.AssignmentStatement(
                                { nl },
                                { binMap[s.kind](Ast.VariableExpression(nl.scope, nl.id), nr) }
                            )
                        else
                            local bId = funcScope:addVariable()
                            local kId = funcScope:addVariable()
                            curStmts[#curStmts + 1] = Ast.LocalVariableDeclaration(funcScope, { bId, kId }, { nl.base, nl.index })
                            funcScope:addReferenceToHigherScope(funcScope, bId, 2)
                            funcScope:addReferenceToHigherScope(funcScope, kId, 2)
                            curStmts[#curStmts + 1] = Ast.AssignmentStatement(
                                { Ast.AssignmentIndexing(Ast.VariableExpression(funcScope, bId), Ast.VariableExpression(funcScope, kId)) },
                                { binMap[s.kind](Ast.IndexExpression(Ast.VariableExpression(funcScope, bId), Ast.VariableExpression(funcScope, kId)), nr) }
                            )
                        end
                    else
                        curStmts[#curStmts + 1] = COMPOUND_CONSTRUCTORS[s.kind](nl, nr)
                    end
                elseif s.kind == AstKind.IfStatement then
                    local function rewriteIfBlock(blk, parentSc)
                        local subSc = Scope:new(parentSc)
                        local subStmts = {}
                        for _, bs in ipairs(blk.statements) do
                            if bs.kind == AstKind.AssignmentStatement then
                                local nl, nr = {}, {}
                                for i = 1, #bs.lhs do nl[i] = rewriteLhs(bs.lhs[i]) end
                                for i = 1, #bs.rhs do nr[i] = rewriteExpr(bs.rhs[i]) end
                                for i = 1, #bs.lhs do
                                    local lk = regKeyOfNode(bs.lhs[i], info)
                                    if lk then
                                        constStrInReg[lk] = nil
                                        constNumInReg[lk] = nil
                                        aliasInReg[lk] = nil
                                        upvalAliasInReg[lk] = nil
                                        tableInReg[lk] = nil
                                        packedInBlock[lk] = nil
                                    end
                                end
                                subStmts[#subStmts + 1] = Ast.AssignmentStatement(nl, nr)
                            elseif bs.kind == AstKind.FunctionCallStatement then
                                local ce = rewriteExpr(Ast.FunctionCallExpression(bs.base, bs.args))
                                if ce.kind == AstKind.FunctionCallExpression then
                                    subStmts[#subStmts + 1] = Ast.FunctionCallStatement(ce.base, ce.args)
                                elseif ce.kind == AstKind.PassSelfFunctionCallExpression then
                                    subStmts[#subStmts + 1] = Ast.PassSelfFunctionCallStatement(ce.base, ce.passSelfFunctionName, ce.args)
                                end
                            elseif bs.kind == AstKind.PassSelfFunctionCallStatement then
                                subStmts[#subStmts + 1] = Ast.PassSelfFunctionCallStatement(rewriteExpr(bs.base), bs.passSelfFunctionName, rewriteArgList(bs.args))
                            elseif bs.kind == AstKind.IfStatement then
                                local subEifs = {}
                                for _, ei in ipairs(bs.elseifs or {}) do
                                    subEifs[#subEifs + 1] = {
                                        condition = rewriteExpr(ei.condition),
                                        body = rewriteIfBlock(ei.body, subSc),
                                    }
                                end
                                subStmts[#subStmts + 1] = Ast.IfStatement(
                                    rewriteExpr(bs.condition),
                                    rewriteIfBlock(bs.body, subSc),
                                    subEifs,
                                    bs.elsebody and rewriteIfBlock(bs.elsebody, subSc) or nil
                                )
                            end
                        end
                        return Ast.Block(subStmts, subSc)
                    end
                    local newCond = rewriteExpr(s.condition)
                    local newBody = rewriteIfBlock(s.body, funcScope)
                    local newEifs = {}
                    for _, ei in ipairs(s.elseifs or {}) do
                        newEifs[#newEifs + 1] = {
                            condition = rewriteExpr(ei.condition),
                            body = rewriteIfBlock(ei.body, funcScope),
                        }
                    end
                    local newElse = s.elsebody and rewriteIfBlock(s.elsebody, funcScope) or nil
                    curStmts[#curStmts + 1] = Ast.IfStatement(newCond, newBody, newEifs, newElse)
                end
                if nb.term.kind == "branch" and nb.term.condPos == idxS then
                    liftedBranchCond = snapshotExprListAtNow({ rewriteExpr(nb.term.cond) })[1]
                end
            end

            local liftedTerm
            if nb.term.kind == "branch" then
                liftedTerm = {
                    kind = "branch",
                    cond = liftedBranchCond or rewriteExpr(nb.term.cond),
                    trueTarget = nb.term.trueTarget,
                    falseTarget = nb.term.falseTarget,
                }
            elseif nb.term.kind == "goto" then
                liftedTerm = { kind = "goto", target = nb.term.target }
            else
                liftedTerm = { kind = "return" }
            end

            liftedBlocks[bIdx] = {
                stmts = curStmts,
                term = liftedTerm,
                returnArgs = blockReturnArgs,
            }
        end

        local blockLocalVarIds = {}
        local allRegVarIds = {}
        for rk, b in pairs(regBinding) do
            if b.kind == "local" then
                allRegVarIds[b.id] = true
                if not upwardExposed[rk] then
                    blockLocalVarIds[b.id] = true
                end
            end
        end
        for sid in pairs(syntheticInlineIds) do
            blockLocalVarIds[sid] = true
            allRegVarIds[sid] = true
        end

        local function isPureTableTree(expr)
            if isPureInlineExpr(expr, funcScope) then return true end
            if expr.kind ~= AstKind.TableConstructorExpression then return false end
            for _, ent in ipairs(expr.entries) do
                if ent.kind == AstKind.KeyedTableEntry then
                    if not isPureTableTree(ent.key) or not isPureTableTree(ent.value) then
                        return false
                    end
                else
                    if not isPureTableTree(ent.value) then
                        return false
                    end
                end
            end
            return true
        end

        for _, bIdx in ipairs(funcNodes) do
            local lb = liftedBlocks[bIdx]
            local stmts = lb.stmts
            for pass = 1, 5 do
                local changedInline = false
                for i = #stmts, 1, -1 do
                    local s = stmts[i]
                    if s and s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                        and s.lhs[1].kind == AstKind.AssignmentVariable
                        and s.lhs[1].scope == funcScope
                        and allRegVarIds[s.lhs[1].id] then
                        local vid = s.lhs[1].id
                        local rhs = s.rhs[1]
                        local isBlockLocal = blockLocalVarIds[vid]

                        local function stmtWritesFuncVar(st, targetVid)
                            if not st then return false end
                            local hit = false
                            visitSub(st, function(n)
                                if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                                if n.kind == AstKind.AssignmentVariable and n.scope == funcScope and n.id == targetVid then
                                    hit = true
                                elseif n.kind == AstKind.LocalVariableDeclaration and n.scope == funcScope then
                                    for _, lid in ipairs(n.ids) do
                                        if lid == targetVid then hit = true end
                                    end
                                end
                            end, nil, info.globalScope)
                            return hit
                        end

                        if rhs.kind == AstKind.NilExpression then
                            local prevWriteIsNil = false
                            local hasEarlierWrite = false
                            for k = i - 1, 1, -1 do
                                local sk = stmts[k]
                                if sk and sk.kind == AstKind.AssignmentStatement then
                                    local wroteVid = false
                                    for _, l in ipairs(sk.lhs) do
                                        if isVarRef(l, funcScope, vid) then
                                            wroteVid = true
                                            hasEarlierWrite = true
                                            if #sk.lhs == 1 and #sk.rhs == 1 and sk.rhs[1].kind == AstKind.NilExpression then
                                                prevWriteIsNil = true
                                            end
                                        end
                                    end
                                    if wroteVid then break end
                                elseif stmtWritesFuncVar(sk, vid) then
                                    hasEarlierWrite = true
                                    break
                                end
                            end
                            local hasLaterRead = false
                            local function checkRead(node)
                                visitSub(node, function(n)
                                    if n.kind == AstKind.VariableExpression and n.scope == funcScope and n.id == vid then
                                        hasLaterRead = true
                                    end
                                end, nil, info.globalScope)
                            end
                            if prevWriteIsNil then
                                table.remove(stmts, i)
                                changedInline = true
                            elseif isBlockLocal and not hasEarlierWrite then
                                for j = i + 1, #stmts do
                                    if stmts[j] then
                                        if stmts[j].kind == AstKind.AssignmentStatement and #stmts[j].lhs == 1
                                            and isVarRef(stmts[j].lhs[1], funcScope, vid) then
                                            checkRead(stmts[j].rhs[1])
                                            break
                                        end
                                        checkRead(stmts[j])
                                    end
                                end
                                if not hasLaterRead and lb.term.kind == "branch" then checkRead(lb.term.cond) end
                                if not hasLaterRead and lb.returnArgs then
                                    for _, ra in ipairs(lb.returnArgs) do checkRead(ra) end
                                end
                                if not hasLaterRead then
                                    table.remove(stmts, i)
                                    changedInline = true
                                end
                            end
                        else
                            local readCount = 0
                            local readStmtIdx = nil
                            local readInCond = false
                            local readInRet = false
                            local killedIdx = nil
                            local abortedByPartialWrite = false

                            local function countVarReads(node)
                                local c = 0
                                visitSub(node, function(n)
                                    if n.kind == AstKind.FunctionLiteralExpression then
                                        local capC = 0
                                        visitSub(n.body, function(m)
                                            if isVarRef(m, funcScope, vid) then capC = capC + 10 end
                                        end, nil, info.globalScope)
                                        c = c + capC
                                        return nil, true
                                    end
                                    if n.kind == AstKind.VariableExpression and n.scope == funcScope and n.id == vid then
                                        c = c + 1
                                    end
                                end, nil, info.globalScope)
                                return c
                            end

                            for j = i + 1, #stmts do
                                local sj = stmts[j]
                                if sj.kind == AstKind.AssignmentStatement and #sj.lhs == 1
                                    and isVarRef(sj.lhs[1], funcScope, vid) then
                                    local rc = countVarReads(sj.rhs[1])
                                    if rc > 0 then
                                        readCount = readCount + rc
                                        readStmtIdx = readStmtIdx or j
                                    end
                                    killedIdx = j
                                    break
                                elseif stmtWritesFuncVar(sj, vid) then
                                    abortedByPartialWrite = true
                                    break
                                else
                                    local rc = countVarReads(sj)
                                    if rc > 0 then
                                        readCount = readCount + rc
                                        readStmtIdx = readStmtIdx or j
                                    end
                                end
                            end

                            if not killedIdx and not abortedByPartialWrite and isBlockLocal then
                                if lb.term.kind == "branch" then
                                    local rc = countVarReads(lb.term.cond)
                                    if rc > 0 then
                                        readCount = readCount + rc
                                        readInCond = true
                                    end
                                end
                                if lb.returnArgs then
                                    for _, ra in ipairs(lb.returnArgs) do
                                        local rc = countVarReads(ra)
                                        if rc > 0 then
                                            readCount = readCount + rc
                                            readInRet = true
                                        end
                                    end
                                end
                            end

                            local canTransform = not abortedByPartialWrite and (isBlockLocal or (killedIdx ~= nil))

                            if canTransform and readCount == 0 then
                                if rhs.kind == AstKind.FunctionCallExpression then
                                    stmts[i] = Ast.FunctionCallStatement(rhs.base, rhs.args)
                                    if isBlockLocal and killedIdx and stmts[killedIdx].rhs[1].kind == AstKind.NilExpression then
                                        table.remove(stmts, killedIdx)
                                    end
                                    changedInline = true
                                elseif rhs.kind == AstKind.PassSelfFunctionCallExpression then
                                    stmts[i] = Ast.PassSelfFunctionCallStatement(rhs.base, rhs.passSelfFunctionName, rhs.args)
                                    if isBlockLocal and killedIdx and stmts[killedIdx].rhs[1].kind == AstKind.NilExpression then
                                        table.remove(stmts, killedIdx)
                                    end
                                    changedInline = true
                                elseif not exprHasCall(rhs, info.globalScope)
                                    and rhs.kind ~= AstKind.IndexExpression
                                    and rhs.kind ~= AstKind.TableConstructorExpression then
                                    local hasPrevNonNilWrite = false
                                    for k = i - 1, 1, -1 do
                                        local sk = stmts[k]
                                        if sk and sk.kind == AstKind.AssignmentStatement then
                                            local wroteVid = false
                                            for _, l in ipairs(sk.lhs) do
                                                if isVarRef(l, funcScope, vid) then
                                                    wroteVid = true
                                                    if not (#sk.lhs == 1 and #sk.rhs == 1 and sk.rhs[1].kind == AstKind.NilExpression) then
                                                        hasPrevNonNilWrite = true
                                                    end
                                                end
                                            end
                                            if wroteVid then break end
                                        elseif stmtWritesFuncVar(sk, vid) then
                                            hasPrevNonNilWrite = true
                                            break
                                        end
                                    end
                                    if not hasPrevNonNilWrite then
                                        table.remove(stmts, i)
                                        changedInline = true
                                    else
                                        stmts[i] = Ast.AssignmentStatement(
                                            { Ast.AssignmentVariable(funcScope, vid) },
                                            { Ast.NilExpression() }
                                        )
                                        changedInline = true
                                    end
                                end
                            elseif canTransform and readCount == 1
                                and (rhs.kind ~= AstKind.TableConstructorExpression
                                    or (readStmtIdx ~= nil and isPureTableTree(rhs)
                                        and stmts[readStmtIdx].kind == AstKind.AssignmentStatement
                                        and #stmts[readStmtIdx].rhs == 1
                                        and stmts[readStmtIdx].rhs[1].kind == AstKind.TableConstructorExpression)) then
                                local rhsDeps = {}
                                visitSub(rhs, function(n)
                                    if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                                    if n.kind == AstKind.VariableExpression and not n.scope.isGlobal and n.scope == funcScope then
                                        rhsDeps[n.id] = true
                                    end
                                end, nil, info.globalScope)
                                local rhsHasCall = exprHasCall(rhs, info.globalScope)
                                local pure = isPureInlineExpr(rhs, funcScope)
                                local isTbl = (rhs.kind == AstKind.TableConstructorExpression)

                                local targetPos = readStmtIdx or (#stmts + 1)
                                local canCommute = true
                                for k = i + 1, targetPos - 1 do
                                    local sk = stmts[k]
                                    for depId in pairs(rhsDeps) do
                                        if stmtWritesFuncVar(sk, depId) then
                                            canCommute = false
                                            break
                                        end
                                    end
                                    if (not pure or isTbl) and stmtHasSideEffect(sk, info.globalScope) then
                                        canCommute = false
                                    end
                                    if rhsHasCall and (not isPureInlineExpr(sk.rhs and sk.rhs[1], funcScope)) then
                                        canCommute = false
                                    end
                                end
                                if canCommute and readStmtIdx and stmts[readStmtIdx].kind == AstKind.IfStatement then
                                    if countVarReads(stmts[readStmtIdx].condition) ~= 1 then
                                        canCommute = false
                                    end
                                end

                                if canCommute and not pure and rhsHasCall then
                                    canCommute = (targetPos == i + 1)
                                end

                                if canCommute then
                                    local replaced = false
                                    local function subInNode(rootNode, isStmt)
                                        local wrapBlk
                                        if isStmt then
                                            wrapBlk = Ast.Block({ rootNode }, funcScope)
                                        else
                                            wrapBlk = Ast.Block({ Ast.ReturnStatement({ rootNode }) }, funcScope)
                                        end
                                        local top = Ast.TopNode(wrapBlk, info.globalScope)
                                        visitast(top, function(n)
                                            if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                                        end, function(n)
                                            if not replaced and n.kind == AstKind.VariableExpression
                                                and n.scope == funcScope and n.id == vid then
                                                replaced = true
                                                return rhs
                                            end
                                        end)
                                        if isStmt then
                                            return top.body.statements[1]
                                        else
                                            return top.body.statements[1].args[1]
                                        end
                                    end

                                    if readStmtIdx then
                                        local okOrder = true
                                        if rhsHasCall then
                                            local sj = stmts[readStmtIdx]
                                            if sj.kind == AstKind.AssignmentStatement and #sj.lhs == 1 and #sj.rhs == 1 then
                                                if sj.lhs[1].kind == AstKind.AssignmentIndexing then okOrder = false end
                                                if not isVarRef(sj.rhs[1], funcScope, vid) then okOrder = false end
                                            else
                                                okOrder = false
                                            end
                                        end
                                        if okOrder then
                                            stmts[readStmtIdx] = subInNode(stmts[readStmtIdx], true)
                                        end
                                    elseif readInCond then
                                        if not rhsHasCall then
                                            lb.term.cond = subInNode(lb.term.cond, false)
                                        end
                                    elseif readInRet and not rhsHasCall then
                                        for rIdx = 1, #lb.returnArgs do
                                            if not replaced then
                                                lb.returnArgs[rIdx] = subInNode(lb.returnArgs[rIdx], false)
                                            end
                                        end
                                    end

                                    if replaced then
                                        table.remove(stmts, i)
                                        changedInline = true
                                    end
                                end
                            end
                        end
                    end
                end
                if not changedInline then break end
            end
        end

        local function succsOf(u)
            local t = liftedBlocks[u].term
            if t.kind == "goto" and t.target and funcNodeSet[t.target] then
                return { t.target }
            elseif t.kind == "branch" then
                local out = {}
                if t.trueTarget and funcNodeSet[t.trueTarget] then out[#out + 1] = t.trueTarget end
                if t.falseTarget and funcNodeSet[t.falseTarget] and t.falseTarget ~= t.trueTarget then
                    out[#out + 1] = t.falseTarget
                end
                return out
            end
            return {}
        end

        local order, idom, preds, dominates, rpoIdx = computeDominators(entryIdx, funcNodes, succsOf)

        local loops = {}
        for _, u in ipairs(order) do
            for _, v in ipairs(succsOf(u)) do
                if dominates(v, u) or (rpoIdx[v] and rpoIdx[u] and rpoIdx[v] <= rpoIdx[u]) then
                    local lp = loops[v]
                    if not lp then
                        lp = { header = v, nodes = { [v] = true }, latchList = {} }
                        loops[v] = lp
                    end
                    lp.latchList[#lp.latchList + 1] = u
                    local stack = { u }
                    while #stack > 0 do
                        local x = table.remove(stack)
                        if not lp.nodes[x] and (rpoIdx[x] or 0) >= (rpoIdx[v] or 0) then
                            lp.nodes[x] = true
                            for _, p in ipairs(preds[x] or {}) do
                                stack[#stack + 1] = p
                            end
                        end
                    end
                end
            end
        end

        for h, lp in pairs(loops) do
            local exitCounts = {}
            local exitNode = nil
            local function voteExit(cand)
                exitCounts[cand] = (exitCounts[cand] or 0) + 1
                if not exitNode or exitCounts[cand] > exitCounts[exitNode]
                    or (exitCounts[cand] == exitCounts[exitNode] and (rpoIdx[cand] or 0) > (rpoIdx[exitNode] or 0)) then
                    exitNode = cand
                end
            end
            for _, u in ipairs(order) do
                if lp.nodes[u] then
                    for _, v in ipairs(succsOf(u)) do
                        if not lp.nodes[v] then
                            local targetExit = v
                            local vb = liftedBlocks[v]
                            if vb and vb.term.kind == "goto" and vb.term.target and not lp.nodes[vb.term.target] then
                                local hasCall = false
                                for _, st in ipairs(vb.stmts) do
                                    if exprHasCall(st, info.globalScope) then hasCall = true break end
                                end
                                if not hasCall then
                                    targetExit = vb.term.target
                                end
                            end
                            voteExit(targetExit)
                        end
                    end
                end
            end
            lp.exit = exitNode
        end

        local function forwardSuccs(u)
            local out = {}
            local ru = rpoIdx[u] or 0
            for _, v in ipairs(succsOf(u)) do
                if not dominates(v, u) and (rpoIdx[v] or 0) > ru then
                    out[#out + 1] = v
                end
            end
            return out
        end

        local activeLoops = {}
        local activePath = {}

        local function emitRegion(startB, stopB, curScope, loopCtx, atTail)
            local out = {}
            local cur = startB
            local seenInRegion = {}

            local function emitContinue()
                if loopCtx then
                    loopCtx.usedContinue = true
                end
                out[#out + 1] = Ast.ContinueStatement()
            end

            while cur do
                if loopCtx then
                    if cur == loopCtx.header and not (cur == startB and loopCtx.justEntered) then
                        if not atTail then
                            emitContinue()
                        end
                        break
                    end
                    if cur == loopCtx.exit then
                        loopCtx.usedBreak = true
                        out[#out + 1] = Ast.BreakStatement()
                        break
                    end
                end
                if stopB and cur == stopB then
                    break
                end
                if seenInRegion[cur] or activePath[cur] then
                    break
                end
                seenInRegion[cur] = true

                local lp = loops[cur]
                if lp and not activeLoops[cur] then
                    activeLoops[cur] = true
                    local bodyScope = Scope:new(curScope)
                    local subLoopCtx = {
                        header = cur,
                        exit = lp.exit,
                        nodes = lp.nodes,
                        justEntered = true,
                        usedContinue = false,
                        usedBreak = false,
                    }
                    local loopBody = emitRegion(cur, lp.exit, bodyScope, subLoopCtx, true)
                    activeLoops[cur] = nil

                    if subLoopCtx.usedContinue and targetLuaVersion == LuaVersion.Lua51 then
                        loopBody = wrapContinueForLua51(loopBody, bodyScope, subLoopCtx.usedBreak)
                    end

                    if #loopBody >= 1 and loopBody[1].kind == AstKind.IfStatement
                        and #loopBody[1].elseifs == 0 and not loopBody[1].elsebody
                        and #loopBody[1].body.statements == 1
                        and loopBody[1].body.statements[1].kind == AstKind.BreakStatement then
                        local wCond = negateExpr(loopBody[1].condition)
                        local rest = {}
                        for i = 2, #loopBody do rest[#rest + 1] = loopBody[i] end
                        out[#out + 1] = Ast.WhileStatement(Ast.Block(rest, bodyScope), wCond, curScope)
                    elseif not subLoopCtx.usedContinue and not subLoopCtx.usedBreak
                        and #loopBody >= 1 and loopBody[#loopBody].kind == AstKind.IfStatement
                        and #loopBody[#loopBody].elseifs == 0 and not loopBody[#loopBody].elsebody
                        and #loopBody[#loopBody].body.statements == 1
                        and loopBody[#loopBody].body.statements[1].kind == AstKind.BreakStatement then
                        local rCond = loopBody[#loopBody].condition
                        local rest = {}
                        for i = 1, #loopBody - 1 do rest[#rest + 1] = loopBody[i] end
                        out[#out + 1] = Ast.RepeatStatement(rCond, Ast.Block(rest, bodyScope), curScope)
                    else
                        out[#out + 1] = Ast.WhileStatement(Ast.Block(loopBody, bodyScope), Ast.BooleanExpression(true), curScope)
                    end

                    cur = lp.exit
                else
                    if loopCtx and cur == loopCtx.header then
                        loopCtx.justEntered = false
                    end

                    local lb = liftedBlocks[cur]
                    for _, s in ipairs(lb.stmts) do
                        out[#out + 1] = s
                    end

                    local t = lb.term
                    if t.kind == "return" then
                        local rArgs = lb.returnArgs or {}
                        if not (isTopLevel and not stopB and atTail and #rArgs == 0) then
                            out[#out + 1] = Ast.ReturnStatement(rArgs)
                        end
                        break
                    elseif t.kind == "goto" then
                        cur = t.target
                    elseif t.kind == "branch" then
                        local tB, fB = t.trueTarget, t.falseTarget

                        if loopCtx and fB == loopCtx.exit and tB ~= loopCtx.exit then
                            local brkScope = Scope:new(curScope)
                            out[#out + 1] = Ast.IfStatement(
                                negateExpr(t.cond),
                                Ast.Block({ Ast.BreakStatement() }, brkScope),
                                {},
                                nil
                            )
                            cur = tB
                        elseif loopCtx and tB == loopCtx.exit and fB ~= loopCtx.exit then
                            local brkScope = Scope:new(curScope)
                            out[#out + 1] = Ast.IfStatement(
                                t.cond,
                                Ast.Block({ Ast.BreakStatement() }, brkScope),
                                {},
                                nil
                            )
                            cur = fB
                        else
                            local function inRegion(v)
                                if not v or v == stopB then return false end
                                if loopCtx then
                                    if v == loopCtx.header or v == loopCtx.exit then return false end
                                    if not loopCtx.nodes[v] then return false end
                                end
                                return funcNodeSet[v] == true
                            end

                            local ipdom, EXIT = computePostDomOnDag(cur, inRegion, forwardSuccs)
                            local rawJoin = ipdom[cur]
                            local joinB = rawJoin
                            if joinB == EXIT then joinB = stopB end
                            local nextCur = joinB
                            if rawJoin == EXIT and loopCtx and stopB == loopCtx.exit then
                                nextCur = nil
                            end

                            local condExpr = t.cond
                            local thenTarget, elseTarget = tB, fB
                            if thenTarget == joinB and elseTarget ~= joinB then
                                condExpr = negateExpr(condExpr)
                                thenTarget, elseTarget = elseTarget, joinB
                            end

                            activePath[cur] = true
                            local thenScope = Scope:new(curScope)
                            local thenTail = (joinB == stopB) and atTail or false
                            local thenStmts = emitRegion(thenTarget, joinB, thenScope, loopCtx, thenTail)

                            local elseStmts = nil
                            local elseScope = nil
                            if elseTarget ~= joinB then
                                elseScope = Scope:new(curScope)
                                local elseTail = (joinB == stopB) and atTail or false
                                elseStmts = emitRegion(elseTarget, joinB, elseScope, loopCtx, elseTail)
                            end
                            activePath[cur] = nil

                            local eifs = {}
                            local finalElseBlk = nil
                            if elseStmts and #elseStmts > 0 then
                                if #elseStmts == 1 and elseStmts[1].kind == AstKind.IfStatement then
                                    local nestedIf = elseStmts[1]
                                    eifs[#eifs + 1] = { condition = nestedIf.condition, body = nestedIf.body }
                                    for _, ne in ipairs(nestedIf.elseifs) do
                                        eifs[#eifs + 1] = ne
                                    end
                                    finalElseBlk = nestedIf.elsebody
                                else
                                    finalElseBlk = Ast.Block(elseStmts, elseScope)
                                end
                            end

                            if #out >= 1 and #eifs == 0 and not finalElseBlk
                                and out[#out].kind == AstKind.AssignmentStatement
                                and #out[#out].lhs == 1 and #out[#out].rhs == 1
                                and out[#out].lhs[1].kind == AstKind.AssignmentVariable
                                and #thenStmts == 1 and thenStmts[1].kind == AstKind.AssignmentStatement
                                and #thenStmts[1].lhs == 1 and #thenStmts[1].rhs == 1
                                and isVarRef(thenStmts[1].lhs[1], out[#out].lhs[1].scope, out[#out].lhs[1].id) then
                                local dstVar = out[#out].lhs[1]
                                local lhsInit = out[#out].rhs[1]
                                local rhsVal = thenStmts[1].rhs[1]
                                if isVarRef(condExpr, dstVar.scope, dstVar.id) then
                                    out[#out] = Ast.AssignmentStatement({ dstVar }, { Ast.AndExpression(lhsInit, rhsVal) })
                                    cur = nextCur
                                elseif condExpr.kind == AstKind.NotExpression and isVarRef(condExpr.rhs, dstVar.scope, dstVar.id) then
                                    out[#out] = Ast.AssignmentStatement({ dstVar }, { Ast.OrExpression(lhsInit, rhsVal) })
                                    cur = nextCur
                                else
                                    out[#out + 1] = Ast.IfStatement(condExpr, Ast.Block(thenStmts, thenScope), eifs, finalElseBlk)
                                    cur = nextCur
                                end
                            else
                                out[#out + 1] = Ast.IfStatement(condExpr, Ast.Block(thenStmts, thenScope), eifs, finalElseBlk)
                                cur = nextCur
                            end
                        end
                    end
                end
            end

            return out
        end

        local bodyStmts = emitRegion(entryIdx, nil, funcScope, nil, true)

        local usedLocalIds = {}
        local bodyDummy = Ast.Block(bodyStmts, funcScope)
        visitSub(bodyDummy, function(n)
            if (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable)
                and n.scope == funcScope then
                usedLocalIds[n.id] = true
            end
        end, nil, info.globalScope)

        local paramSet = {}
        for _, pid in ipairs(paramIds) do paramSet[pid] = true end

        local declIds = {}
        local declaredSet = {}
        for _, rk in ipairs(regOrder) do
            local b = regBinding[rk]
            if b and b.kind == "local" and usedLocalIds[b.id] and not paramSet[b.id] then
                declIds[#declIds + 1] = b.id
                declaredSet[b.id] = true
            end
        end
        local extraSids = {}
        for sid in pairs(syntheticInlineIds) do
            if usedLocalIds[sid] and not declaredSet[sid] and not paramSet[sid] then
                extraSids[#extraSids + 1] = sid
            end
        end
        table.sort(extraSids)
        for _, sid in ipairs(extraSids) do
            declIds[#declIds + 1] = sid
        end

        local headerDecls = {}
        if varargTableVarId and usedLocalIds[varargTableVarId] then
            headerDecls[#headerDecls + 1] = Ast.LocalVariableDeclaration(funcScope, { varargTableVarId }, {})
        end
        if localSpillId and usedLocalIds[localSpillId] then
            headerDecls[#headerDecls + 1] = Ast.LocalVariableDeclaration(
                funcScope,
                { localSpillId },
                { Ast.TableConstructorExpression({}) }
            )
        end
        if #declIds > 0 then
            headerDecls[#headerDecls + 1] = Ast.LocalVariableDeclaration(funcScope, declIds, {})
        end
        if isTopLevel and info.topUpvalCount > 0 then
            for u = 1, info.topUpvalCount do
                local uv = parentUpvals[u]
                if uv and usedLocalIds[uv.id] then
                    table.insert(headerDecls, 1, Ast.LocalVariableDeclaration(
                        funcScope,
                        { uv.id },
                        { Ast.TableConstructorExpression({}) }
                    ))
                end
            end
        end

        local finalStmts = {}
        for i = 1, #headerDecls do finalStmts[#finalStmts + 1] = headerDecls[i] end
        for i = 1, #bodyStmts do finalStmts[#finalStmts + 1] = bodyStmts[i] end

        local resultBlock = Ast.Block(finalStmts, funcScope)
        rebindScopesInSubtree(resultBlock, funcScope, info.globalScope)

        if isTopLevel then
            return resultBlock
        else
            return Ast.FunctionLiteralExpression(fnArgs, resultBlock)
        end
    end

    local topUpvals = {}
    for u = 1, info.topUpvalCount do
        local uid = holderScope:addVariable()
        topUpvals[u] = { scope = holderScope, id = uid }
    end

    local liftedTop = liftClosure(info.startBlockId, true, true, topUpvals, holderScope)
    if not liftedTop then return nil end

    if helperVars.unpack and helperVars.pack then
        local function unwrapUnpackPack(e)
            if e and e.kind == AstKind.FunctionCallExpression
                and isVarRef(e.base, holderScope, helperVars.unpack)
                and #e.args == 1
                and e.args[1].kind == AstKind.FunctionCallExpression
                and isVarRef(e.args[1].base, holderScope, helperVars.pack)
                and #e.args[1].args == 1 then
                return e.args[1].args[1]
            end
            return nil
        end
        local wrapTop = Ast.TopNode(Ast.Block({ Ast.DoStatement(liftedTop) }, holderScope), info.globalScope)
        visitast(wrapTop, nil, function(n)
            if n.kind == AstKind.ReturnStatement and #n.args == 1 then
                local inner = unwrapUnpackPack(n.args[1])
                if inner then n.args[1] = inner end
            elseif (n.kind == AstKind.FunctionCallExpression or n.kind == AstKind.FunctionCallStatement
                or n.kind == AstKind.PassSelfFunctionCallExpression or n.kind == AstKind.PassSelfFunctionCallStatement)
                and #n.args >= 1 then
                local inner = unwrapUnpackPack(n.args[#n.args])
                if inner then n.args[#n.args] = inner end
            elseif n.kind == AstKind.TableConstructorExpression and #n.entries >= 1 then
                local last = n.entries[#n.entries]
                if last.kind == AstKind.TableEntry then
                    local inner = unwrapUnpackPack(last.value)
                    if inner then last.value = inner end
                end
            end
        end)
    end

    local usedInHolder = {}
    visitSub(liftedTop, function(n)
        if (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable)
            and n.scope == holderScope then
            usedInHolder[n.id] = true
        end
    end, nil, info.globalScope)

    local topDecls = {}
    local function gRef(name)
        local _, gid = info.globalScope:resolve(name)
        holderScope:addReferenceToHigherScope(info.globalScope, gid)
        return Ast.VariableExpression(info.globalScope, gid)
    end

    if helperVars.tonumber and usedInHolder[helperVars.tonumber] then
        topDecls[#topDecls + 1] = Ast.LocalVariableDeclaration(holderScope, { helperVars.tonumber }, { gRef("tonumber") })
    end
    if helperVars.error and usedInHolder[helperVars.error] then
        topDecls[#topDecls + 1] = Ast.LocalVariableDeclaration(holderScope, { helperVars.error }, { gRef("error") })
    end
    local needSelectForPack = helperVars.pack and usedInHolder[helperVars.pack]
    local selLocalId = helperVars.select
    if (selLocalId and usedInHolder[selLocalId]) or needSelectForPack then
        selLocalId = getHelperVar("select")
        topDecls[#topDecls + 1] = Ast.LocalVariableDeclaration(holderScope, { selLocalId }, { gRef("select") })
    end
    if needSelectForPack then
        local pkScope = Scope:new(holderScope)
        pkScope:addReferenceToHigherScope(holderScope, selLocalId)
        topDecls[#topDecls + 1] = Ast.LocalFunctionDeclaration(
            holderScope,
            helperVars.pack,
            { Ast.VarargExpression() },
            Ast.Block({
                Ast.ReturnStatement({
                    Ast.TableConstructorExpression({
                        Ast.KeyedTableEntry(
                            Ast.StringExpression("n"),
                            Ast.FunctionCallExpression(
                                Ast.VariableExpression(holderScope, selLocalId),
                                { Ast.StringExpression("#"), Ast.VarargExpression() }
                            )
                        ),
                        Ast.TableEntry(Ast.VarargExpression()),
                    }),
                }),
            }, pkScope)
        )
    end
    if helperVars.unpack and usedInHolder[helperVars.unpack] then
        local upkRawId = holderScope:addVariable()
        topDecls[#topDecls + 1] = Ast.LocalVariableDeclaration(
            holderScope,
            { upkRawId },
            { Ast.OrExpression(gRef("unpack"), Ast.IndexExpression(gRef("table"), Ast.StringExpression("unpack"))) }
        )
        local uScope = Scope:new(holderScope)
        local uParam = uScope:addVariable()
        uScope:addReferenceToHigherScope(holderScope, upkRawId)
        uScope:addReferenceToHigherScope(uScope, uParam, 2)
        topDecls[#topDecls + 1] = Ast.LocalFunctionDeclaration(
            holderScope,
            helperVars.unpack,
            { Ast.VariableExpression(uScope, uParam) },
            Ast.Block({
                Ast.ReturnStatement({
                    Ast.FunctionCallExpression(
                        Ast.VariableExpression(holderScope, upkRawId),
                        {
                            Ast.VariableExpression(uScope, uParam),
                            Ast.NumberExpression(1),
                            Ast.IndexExpression(Ast.VariableExpression(uScope, uParam), Ast.StringExpression("n")),
                        }
                    ),
                }),
            }, uScope)
        )
    end

    for u = 1, info.topUpvalCount do
        local uid = topUpvals[u].id
        if usedInHolder[uid] then
            topDecls[#topDecls + 1] = Ast.LocalVariableDeclaration(
                holderScope,
                { uid },
                { Ast.TableConstructorExpression({}) }
            )
        end
    end

    if #topDecls > 0 then
        local outScope = liftedTop.scope
        local holderToOut = {}
        local function mapHolderId(hid)
            if not holderToOut[hid] then
                holderToOut[hid] = outScope:addVariable(holderScope:getVariableName(hid))
            end
            return holderToOut[hid]
        end
        for i = 1, #liftedTop.statements do
            topDecls[#topDecls + 1] = liftedTop.statements[i]
        end
        liftedTop.statements = topDecls
        visitSub(liftedTop, function(n)
            if n.kind == AstKind.LocalVariableDeclaration and n.scope == holderScope then
                n.scope = outScope
                for j = 1, #n.ids do n.ids[j] = mapHolderId(n.ids[j]) end
            elseif (n.kind == AstKind.LocalFunctionDeclaration or n.kind == AstKind.FunctionDeclaration)
                and n.scope == holderScope then
                n.scope = outScope
                n.id = mapHolderId(n.id)
            elseif (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable)
                and n.scope == holderScope then
                n.scope = outScope
                n.id = mapHolderId(n.id)
            end
        end, nil, info.globalScope)
        local function purgeHolder(sc)
            if not sc then return end
            if sc.variablesFromHigherScopes then
                sc.variablesFromHigherScopes[holderScope] = nil
            end
            for _, ch in ipairs(sc.children or {}) do
                purgeHolder(ch)
            end
        end
        purgeHolder(holderScope)
        purgeHolder(outScope)
        outScope:setParent(topParentScope)
        local hChildren = {}
        for _, hc in ipairs(holderScope.children or {}) do
            if hc ~= outScope then hChildren[#hChildren + 1] = hc end
        end
        for _, hc in ipairs(hChildren) do
            hc:setParent(outScope)
        end
        if holderScope.parentScope then
            holderScope.parentScope:removeChild(holderScope)
        end
        rebindScopesInSubtree(liftedTop, topParentScope, info.globalScope)
        return liftedTop
    end

    liftedTop.scope:setParent(topParentScope)
    return liftedTop
end

function CffDecompiler.unflatten(ast, targetLuaVersion)
    targetLuaVersion = targetLuaVersion or LuaVersion.Lua51
    local changed = false

    visitast(ast, nil, function(node)
        if node.kind == AstKind.FunctionLiteralExpression and node.body then
            local info = matchCffContainer(node.body, ast.globalScope)
            if info then
                local lifted = liftContainer(node.body, info, targetLuaVersion)
                if lifted then
                    local prefix = {}
                    for i = 1, #node.body.statements - 1 do
                        prefix[#prefix + 1] = node.body.statements[i]
                    end
                    if #prefix == 0 then
                        local oldFnScope = node.body.scope
                        for _, arg in ipairs(node.args) do
                            if arg.kind == AstKind.VariableExpression then
                                local newId = lifted.scope:addVariable()
                                visitSub(lifted, function(m)
                                    if (m.kind == AstKind.VariableExpression or m.kind == AstKind.AssignmentVariable)
                                        and m.scope == arg.scope and m.id == arg.id then
                                        m.scope = lifted.scope
                                        m.id = newId
                                    end
                                end, nil, ast.globalScope)
                                arg.scope = lifted.scope
                                arg.id = newId
                            end
                        end
                        local function purgeFnSc(sc)
                            if not sc then return end
                            if sc.variablesFromHigherScopes then
                                sc.variablesFromHigherScopes[oldFnScope] = nil
                            end
                            for _, ch in ipairs(sc.children or {}) do purgeFnSc(ch) end
                        end
                        purgeFnSc(lifted.scope)
                        lifted.scope:setParent(oldFnScope.parentScope or ast.globalScope)
                        if oldFnScope.parentScope then
                            oldFnScope.parentScope:removeChild(oldFnScope)
                        end
                        node.body = lifted
                    else
                        lifted.scope:setParent(node.body.scope)
                        prefix[#prefix + 1] = Ast.DoStatement(lifted)
                        node.body.statements = prefix
                    end
                    changed = true
                end
            end
        end
    end)

    local topInfo = matchCffContainer(ast.body, ast.globalScope)
    if topInfo then
        local lifted = liftContainer(ast.body, topInfo, targetLuaVersion)
        if lifted then
            if #ast.body.statements == 1 or topInfo.pureOuterSetup then
                local oldTopScope = ast.body.scope
                local function purgeTopSc(sc)
                    if not sc then return end
                    if sc.variablesFromHigherScopes then
                        sc.variablesFromHigherScopes[oldTopScope] = nil
                    end
                    for _, ch in ipairs(sc.children or {}) do purgeTopSc(ch) end
                end
                purgeTopSc(lifted.scope)
                lifted.scope:setParent(ast.globalScope)
                if oldTopScope and oldTopScope.parentScope then
                    oldTopScope.parentScope:removeChild(oldTopScope)
                end
                ast.body = lifted
            else
                lifted.scope:setParent(ast.body.scope)
                ast.body.statements[#ast.body.statements] = Ast.DoStatement(lifted)
            end
            changed = true
        end
    end

    return changed
end

function CffDecompiler.detect(ast)
    if ast.body and matchCffContainer(ast.body, ast.globalScope) then
        return { present = true, ready = true, topLevel = true }
    end
    local nestedReady = false
    local candidateEnvelope = false
    visitast(ast, function(node)
        if node.kind == AstKind.FunctionLiteralExpression and node.body then
            if matchCffContainer(node.body, ast.globalScope) then
                nestedReady = true
            end
        elseif node.kind == AstKind.FunctionCallExpression
            and node.base.kind == AstKind.FunctionLiteralExpression
            and #node.args == 11 and #node.base.args >= 23 then
            candidateEnvelope = true
        end
    end)
    if nestedReady then
        return { present = true, ready = true, topLevel = false }
    elseif candidateEnvelope then
        return { present = true, ready = false, topLevel = false }
    end
    return nil
end

return CffDecompiler

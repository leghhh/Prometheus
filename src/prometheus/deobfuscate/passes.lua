local Ast = require("prometheus.ast")
local Scope = require("prometheus.scope")
local visitast = require("prometheus.visitast")
local util = require("prometheus.util")

local AstKind = Ast.AstKind
local lookupify = util.lookupify

local Passes = {}

local function visitNode(node, previsit, postvisit, globalScope)
    if node.kind == AstKind.TopNode then
        return visitast(node, previsit, postvisit)
    end
    local gs = globalScope
    if not gs then
        local sc = node.scope or (node.body and node.body.scope)
        while sc and sc.parentScope do
            sc = sc.parentScope
        end
        gs = sc
    end
    if node.kind == AstKind.Block then
        return visitast(Ast.TopNode(node, gs), previsit, postvisit)
    end
    if not string.find(node.kind, "Expression", 1, true) then
        local blk = Ast.Block({ node }, node.scope or gs)
        visitast(Ast.TopNode(blk, gs), previsit, postvisit)
        return blk.statements[1]
    end
    local ret = Ast.ReturnStatement({ node })
    local blk = Ast.Block({ ret }, gs)
    visitast(Ast.TopNode(blk, gs), previsit, postvisit)
    return ret.args[1]
end

local function varKey(scope, id)
    return tostring(scope) .. ":" .. tostring(id)
end

local function isVarRef(node, scope, id)
    return node and node.kind == AstKind.VariableExpression and node.scope == scope and node.id == id
end

local function isGlobalVar(node, name)
    return node and node.kind == AstKind.VariableExpression and node.scope and node.scope.isGlobal
        and node.scope:getVariableName(node.id) == name
end

local function countVarUsage(ast)
    local reads = {}
    local writes = {}
    visitast(ast, function(node)
        if node.kind == AstKind.VariableExpression then
            local k = varKey(node.scope, node.id)
            reads[k] = (reads[k] or 0) + 1
        elseif node.kind == AstKind.AssignmentVariable then
            local k = varKey(node.scope, node.id)
            writes[k] = (writes[k] or 0) + 1
        elseif node.kind == AstKind.FunctionDeclaration then
            local k = varKey(node.scope, node.id)
            if node.indices and #node.indices > 0 then
                reads[k] = (reads[k] or 0) + 1
            else
                writes[k] = (writes[k] or 0) + 1
            end
        elseif node.kind == AstKind.LocalFunctionDeclaration then
            local k = varKey(node.scope, node.id)
            writes[k] = (writes[k] or 0) + 1
        elseif node.kind == AstKind.LocalVariableDeclaration then
            if node.expressions and #node.expressions > 0 then
                for i = 1, #node.ids do
                    local k = varKey(node.scope, node.ids[i])
                    writes[k] = (writes[k] or 0) + 1
                end
            end
        end
    end)
    return reads, writes
end

local function makeConstantNode(val)
    if val == nil then
        return Ast.NilExpression()
    end
    local t = type(val)
    if t == "boolean" then
        return Ast.BooleanExpression(val)
    end
    if t == "string" then
        return Ast.StringExpression(val)
    end
    if t == "number" then
        return Ast.NumberExpression(val)
    end
    return nil
end

local BINARY_EVAL = {
    [AstKind.AddExpression] = function(a, b)
        if type(a) == "number" and type(b) == "number" then return true, a + b end
        return false
    end,
    [AstKind.SubExpression] = function(a, b)
        if type(a) == "number" and type(b) == "number" then return true, a - b end
        return false
    end,
    [AstKind.MulExpression] = function(a, b)
        if type(a) == "number" and type(b) == "number" then return true, a * b end
        return false
    end,
    [AstKind.DivExpression] = function(a, b)
        if type(a) == "number" and type(b) == "number" then
            if b == 0 and a == 0 then return true, 0 / 0 end
            if b ~= 0 then return true, a / b end
        end
        return false
    end,
    [AstKind.ModExpression] = function(a, b)
        if type(a) == "number" and type(b) == "number" and b ~= 0 then
            return true, a % b
        end
        return false
    end,
    [AstKind.PowExpression] = function(a, b)
        if type(a) == "number" and type(b) == "number" then return true, a ^ b end
        return false
    end,
    [AstKind.LessThanExpression] = function(a, b)
        if (type(a) == "number" and type(b) == "number") or (type(a) == "string" and type(b) == "string") then
            return true, a < b
        end
        return false
    end,
    [AstKind.GreaterThanExpression] = function(a, b)
        if (type(a) == "number" and type(b) == "number") or (type(a) == "string" and type(b) == "string") then
            return true, a > b
        end
        return false
    end,
    [AstKind.LessThanOrEqualsExpression] = function(a, b)
        if (type(a) == "number" and type(b) == "number") or (type(a) == "string" and type(b) == "string") then
            return true, a <= b
        end
        return false
    end,
    [AstKind.GreaterThanOrEqualsExpression] = function(a, b)
        if (type(a) == "number" and type(b) == "number") or (type(a) == "string" and type(b) == "string") then
            return true, a >= b
        end
        return false
    end,
    [AstKind.EqualsExpression] = function(a, b)
        return true, a == b
    end,
    [AstKind.NotEqualsExpression] = function(a, b)
        return true, a ~= b
    end,
}

local function isConstantLiteral(node)
    if not node then return false end
    local k = node.kind
    return k == AstKind.NumberExpression
        or k == AstKind.StringExpression
        or k == AstKind.BooleanExpression
        or k == AstKind.NilExpression
end

function Passes.foldConstants(ast)
    local changes = 0
    visitast(ast, nil, function(node)
        local kind = node.kind
        if kind == AstKind.NegateExpression and node.rhs.kind == AstKind.NumberExpression then
            local v = node.rhs.value
            local res = (v == 0) and (-tonumber("0")) or (-v)
            changes = changes + 1
            return Ast.NumberExpression(res)
        end
        if kind == AstKind.NotExpression and isConstantLiteral(node.rhs) then
            changes = changes + 1
            return Ast.BooleanExpression(not node.rhs.value)
        end
        if kind == AstKind.LenExpression and node.rhs.kind == AstKind.StringExpression then
            changes = changes + 1
            return Ast.NumberExpression(#node.rhs.value)
        end
        if kind == AstKind.StrCatExpression then
            if node.lhs.kind == AstKind.StringExpression and node.rhs.kind == AstKind.StringExpression then
                changes = changes + 1
                return Ast.StringExpression(node.lhs.value .. node.rhs.value)
            end
            if node.lhs.kind == AstKind.StringExpression and node.rhs.kind == AstKind.StrCatExpression
                and node.rhs.lhs.kind == AstKind.StringExpression then
                changes = changes + 1
                return Ast.StrCatExpression(
                    Ast.StringExpression(node.lhs.value .. node.rhs.lhs.value),
                    node.rhs.rhs,
                    false
                )
            end
        end
        if kind == AstKind.AndExpression and isConstantLiteral(node.lhs) then
            if not node.lhs.value then
                changes = changes + 1
                return makeConstantNode(node.lhs.value)
            elseif isConstantLiteral(node.rhs) then
                changes = changes + 1
                return makeConstantNode(node.rhs.value)
            end
        end
        if kind == AstKind.OrExpression and isConstantLiteral(node.lhs) then
            if node.lhs.value then
                changes = changes + 1
                return makeConstantNode(node.lhs.value)
            elseif isConstantLiteral(node.rhs) then
                changes = changes + 1
                return makeConstantNode(node.rhs.value)
            end
        end
        local eval = BINARY_EVAL[kind]
        if eval and isConstantLiteral(node.lhs) and isConstantLiteral(node.rhs) then
            local ok, res = eval(node.lhs.value, node.rhs.value)
            if ok then
                local replacement = makeConstantNode(res)
                if replacement then
                    changes = changes + 1
                    return replacement
                end
            end
        end
    end)
    return changes > 0
end

local function effectiveArgCount(args)
    local n = #args
    if n > 0 and args[n].kind == AstKind.VarargExpression then
        return n - 1, true
    end
    return n, false
end

function Passes.unwrapFunction(ast)
    local unwrapped = false
    while true do
        local stmts = ast.body and ast.body.statements
        if not stmts or #stmts == 0 then break end
        local ret = stmts[#stmts]
        if ret.kind ~= AstKind.ReturnStatement or #ret.args ~= 1 then break end
        local call = ret.args[1]
        if call.kind ~= AstKind.FunctionCallExpression or call.isParenthesizedExpression then break end
        if #call.args ~= 1 or call.args[1].kind ~= AstKind.VarargExpression then break end
        local fn = call.base
        if fn.kind ~= AstKind.FunctionLiteralExpression then break end
        if #fn.args ~= 1 or fn.args[1].kind ~= AstKind.VarargExpression then break end

        if #stmts == 1 then
            fn.body.scope:setParent(ast.globalScope)
            ast.body = fn.body
        else
            fn.body.scope:setParent(ast.body.scope)
            table.remove(stmts, #stmts)
            for i = 1, #fn.body.statements do
                stmts[#stmts + 1] = fn.body.statements[i]
            end
        end
        unwrapped = true
    end
    return unwrapped
end

function Passes.unwrapFlattenVmBridge(ast)
    local changed = false
    visitast(ast, nil, function(node)
        if node.kind ~= AstKind.FunctionLiteralExpression then return end
        if #node.args ~= 1 or node.args[1].kind ~= AstKind.VarargExpression then return end
        local stmts = node.body.statements
        if #stmts ~= 1 or stmts[1].kind ~= AstKind.ReturnStatement or #stmts[1].args ~= 1 then return end
        local outerCall = stmts[1].args[1]
        if outerCall.kind ~= AstKind.FunctionCallExpression or outerCall.isParenthesizedExpression then return end
        local innerFn = outerCall.base
        if innerFn.kind ~= AstKind.FunctionLiteralExpression then return end
        if #innerFn.args ~= 1 or innerFn.args[1].kind ~= AstKind.VarargExpression then return end

        local callArgs = outerCall.args
        if #callArgs < 1 or callArgs[#callArgs].kind ~= AstKind.VarargExpression then return end
        local extCount = #callArgs - 1
        for i = 1, extCount do
            if callArgs[i].kind ~= AstKind.VariableExpression then return end
        end

        local innerStmts = innerFn.body.statements
        if extCount == 0 then
            if #innerStmts ~= 1 or innerStmts[1].kind ~= AstKind.ReturnStatement or #innerStmts[1].args ~= 1 then return end
            local retCall = innerStmts[1].args[1]
            if retCall.kind ~= AstKind.FunctionCallExpression or retCall.isParenthesizedExpression then return end
            if #retCall.args ~= 1 or retCall.args[1].kind ~= AstKind.VarargExpression then return end
            if retCall.base.kind ~= AstKind.FunctionLiteralExpression then return end
            changed = true
            return retCall.base
        else
            if #innerStmts == 2 then
                local decl = innerStmts[1]
                local ret = innerStmts[2]
                if decl.kind ~= AstKind.LocalVariableDeclaration or #decl.ids ~= extCount then return end
                if #decl.expressions ~= 1 or decl.expressions[1].kind ~= AstKind.VarargExpression then return end
                if ret.kind ~= AstKind.ReturnStatement or #ret.args ~= 1 then return end
                local retCall = ret.args[1]
                if retCall.kind ~= AstKind.FunctionCallExpression or retCall.isParenthesizedExpression then return end
                if retCall.base.kind ~= AstKind.FunctionLiteralExpression then return end
                if #retCall.args ~= 1 or retCall.args[1].kind ~= AstKind.FunctionCallExpression then return end
                local selCall = retCall.args[1]
                if selCall.base.kind ~= AstKind.VariableExpression or not selCall.base.scope.isGlobal then return end
                if selCall.base.scope:getVariableName(selCall.base.id) ~= "select" then return end
                if #selCall.args ~= 2 or selCall.args[1].kind ~= AstKind.NumberExpression then return end
                if selCall.args[1].value ~= extCount + 1 or selCall.args[2].kind ~= AstKind.VarargExpression then return end

                local map = {}
                for i = 1, extCount do
                    map[varKey(decl.scope, decl.ids[i])] = callArgs[i]
                end
                local runtimeFn = retCall.base
                visitNode(runtimeFn, function(n)
                    if n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable or n.kind == AstKind.FunctionDeclaration then
                        local target = map[varKey(n.scope, n.id)]
                        if target then
                            n.scope = target.scope
                            n.id = target.id
                        end
                    end
                end, nil, ast.globalScope)
                runtimeFn.body.scope:setParent(node.body.scope.parentScope or ast.globalScope)
                changed = true
                return runtimeFn
            elseif #innerStmts >= 3 then
                local ret = innerStmts[#innerStmts]
                if ret.kind ~= AstKind.ReturnStatement or #ret.args ~= 1 then return end
                local retCall = ret.args[1]
                if retCall.kind ~= AstKind.FunctionCallExpression or retCall.isParenthesizedExpression then return end
                if retCall.base.kind ~= AstKind.FunctionLiteralExpression then return end
                if #retCall.args ~= 1 or retCall.args[1].kind ~= AstKind.FunctionCallExpression then return end
                local selCall = retCall.args[1]
                if #selCall.args ~= 2 or selCall.args[1].kind ~= AstKind.NumberExpression then return end
                if selCall.args[1].value ~= extCount + 1 or selCall.args[2].kind ~= AstKind.VarargExpression then return end

                local selectAliases = {}
                local varargTblScope, varargTblId
                for i = 1, #innerStmts - 1 do
                    local st = innerStmts[i]
                    if st.kind == AstKind.LocalVariableDeclaration and #st.ids == 1 and #st.expressions == 1 then
                        local ex = st.expressions[1]
                        if ex.kind == AstKind.VariableExpression and ex.scope.isGlobal
                            and ex.scope:getVariableName(ex.id) == "select" then
                            selectAliases[varKey(st.scope, st.ids[1])] = true
                        end
                    elseif st.kind == AstKind.AssignmentStatement and #st.lhs == 1 and #st.rhs == 1
                        and st.lhs[1].kind == AstKind.AssignmentVariable
                        and st.rhs[1].kind == AstKind.TableConstructorExpression
                        and #st.rhs[1].entries == 1
                        and st.rhs[1].entries[1].kind == AstKind.TableEntry
                        and st.rhs[1].entries[1].value.kind == AstKind.VarargExpression then
                        varargTblScope, varargTblId = st.lhs[1].scope, st.lhs[1].id
                    end
                end

                local isSelectBase = false
                if selCall.base.kind == AstKind.VariableExpression then
                    if selCall.base.scope.isGlobal and selCall.base.scope:getVariableName(selCall.base.id) == "select" then
                        isSelectBase = true
                    elseif selectAliases[varKey(selCall.base.scope, selCall.base.id)] then
                        isSelectBase = true
                    end
                end
                if not isSelectBase or not varargTblScope then return end

                visitNode(innerFn.body, nil, function(n)
                    if n.kind == AstKind.IndexExpression
                        and isVarRef(n.base, varargTblScope, varargTblId)
                        and n.index.kind == AstKind.NumberExpression then
                        local pos = n.index.value
                        if pos >= 1 and pos <= extCount then
                            return Ast.VariableExpression(callArgs[pos].scope, callArgs[pos].id)
                        end
                    end
                end, ast.globalScope)

                local aliasToExt = {}
                for pass = 1, 3 do
                    for i = 1, #innerStmts - 1 do
                        local st = innerStmts[i]
                        if st.kind == AstKind.LocalVariableDeclaration and #st.ids == 1 and #st.expressions == 1
                            and st.expressions[1].kind == AstKind.VariableExpression then
                            local rhsV = st.expressions[1]
                            local mapped = aliasToExt[varKey(rhsV.scope, rhsV.id)]
                            if not mapped then
                                for c = 1, extCount do
                                    if isVarRef(rhsV, callArgs[c].scope, callArgs[c].id) then
                                        mapped = callArgs[c]
                                        break
                                    end
                                end
                            end
                            if mapped then
                                aliasToExt[varKey(st.scope, st.ids[1])] = mapped
                            end
                        elseif st.kind == AstKind.AssignmentStatement and #st.lhs == 1 and #st.rhs == 1
                            and st.lhs[1].kind == AstKind.AssignmentVariable
                            and st.rhs[1].kind == AstKind.VariableExpression then
                            local rhsV = st.rhs[1]
                            local mapped = aliasToExt[varKey(rhsV.scope, rhsV.id)]
                            if not mapped then
                                for c = 1, extCount do
                                    if isVarRef(rhsV, callArgs[c].scope, callArgs[c].id) then
                                        mapped = callArgs[c]
                                        break
                                    end
                                end
                            end
                            if mapped then
                                aliasToExt[varKey(st.lhs[1].scope, st.lhs[1].id)] = mapped
                            end
                        end
                    end
                end

                local runtimeFn = retCall.base
                local movedHelpers = {}
                local helperRemap = {}
                local allowedHelperScopes = {}
                local candidateHelpers = {}
                local candidateHelperKeys = {}
                local allowedHelperScopes = {}
                for i = 1, #innerStmts - 1 do
                    local st = innerStmts[i]
                    if st.kind == AstKind.LocalVariableDeclaration and st.expressions and #st.expressions > 0 then
                        local usesVararg = false
                        for _, ex in ipairs(st.expressions) do
                            visitNode(ex, function(n)
                                if n.kind == AstKind.VarargExpression or isVarRef(n, varargTblScope, varargTblId) then
                                    usesVararg = true
                                end
                            end, nil, ast.globalScope)
                        end
                        if not usesVararg then
                            for _, oldId in ipairs(st.ids) do
                                candidateHelperKeys[varKey(st.scope, oldId)] = true
                            end
                            candidateHelpers[#candidateHelpers + 1] = st
                        end
                    elseif st.kind == AstKind.LocalFunctionDeclaration then
                        local usesVarargTbl = false
                        visitNode(st.body, function(n)
                            if isVarRef(n, varargTblScope, varargTblId) then
                                usesVarargTbl = true
                            end
                        end, nil, ast.globalScope)
                        if not usesVarargTbl then
                            candidateHelperKeys[varKey(st.scope, st.id)] = true
                            visitNode(st.body, function(n)
                                if n.kind == AstKind.Block and n.scope and not n.scope.isGlobal then
                                    allowedHelperScopes[n.scope] = true
                                end
                            end, nil, ast.globalScope)
                            candidateHelpers[#candidateHelpers + 1] = st
                        end
                    end
                end

                local stillRefsInner = false
                local innerScopes = {}
                visitNode(innerFn.body, function(n)
                    if n == runtimeFn then return nil, true end
                    if n.kind == AstKind.Block and n.scope and not n.scope.isGlobal and not allowedHelperScopes[n.scope] then
                        innerScopes[n.scope] = true
                    end
                end, nil, ast.globalScope)
                innerScopes[innerFn.body.scope] = true

                visitNode(runtimeFn, function(n)
                    if n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable then
                        local k = varKey(n.scope, n.id)
                        if not aliasToExt[k] and not candidateHelperKeys[k] and innerScopes[n.scope] then
                            stillRefsInner = true
                        end
                    end
                end, nil, ast.globalScope)

                if not stillRefsInner then
                    local movedHelpers = {}
                    local helperRemap = {}
                    for _, st in ipairs(candidateHelpers) do
                        if st.kind == AstKind.LocalVariableDeclaration then
                            local newIds = {}
                            for _, oldId in ipairs(st.ids) do
                                local nid = runtimeFn.body.scope:addVariable()
                                helperRemap[varKey(st.scope, oldId)] = { scope = runtimeFn.body.scope, id = nid }
                                newIds[#newIds + 1] = nid
                            end
                            movedHelpers[#movedHelpers + 1] = Ast.LocalVariableDeclaration(runtimeFn.body.scope, newIds, st.expressions)
                        elseif st.kind == AstKind.LocalFunctionDeclaration then
                            local nid = runtimeFn.body.scope:addVariable()
                            helperRemap[varKey(st.scope, st.id)] = { scope = runtimeFn.body.scope, id = nid }
                            visitNode(st.body, function(n)
                                if n.kind == AstKind.Block and n.scope and not n.scope.isGlobal then
                                    n.scope.variablesFromHigherScopes = {}
                                    n.scope.referenceCounts = {}
                                end
                            end, nil, ast.globalScope)
                            st.body.scope.parentScope = runtimeFn.body.scope
                            movedHelpers[#movedHelpers + 1] = Ast.LocalFunctionDeclaration(runtimeFn.body.scope, nid, st.args, st.body)
                        end
                    end

                    for _, mh in ipairs(movedHelpers) do
                        visitNode(mh, function(n)
                            if n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable then
                                local hm = helperRemap[varKey(n.scope, n.id)]
                                if hm then
                                    n.scope = hm.scope
                                    n.id = hm.id
                                end
                            end
                        end, nil, ast.globalScope)
                    end

                    visitNode(runtimeFn, function(n)
                        if n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable then
                            local target = aliasToExt[varKey(n.scope, n.id)] or helperRemap[varKey(n.scope, n.id)]
                            if target then
                                n.scope = target.scope
                                n.id = target.id
                            end
                        end
                    end, nil, ast.globalScope)

                    for i = #movedHelpers, 1, -1 do
                        table.insert(runtimeFn.body.statements, 1, movedHelpers[i])
                    end
                    runtimeFn.body.scope.parentScope = node.body.scope.parentScope or ast.globalScope
                    changed = true
                    return runtimeFn
                end
            end
        end
    end)
    return changed
end

local function isAntiTamperDoBlock(stmt)
    if stmt.kind ~= AstKind.DoStatement then return false end
    local body = stmt.body
    local stmts = body.statements
    if #stmts < 5 then return false end
    if stmts[1].kind ~= AstKind.LocalVariableDeclaration or #stmts[1].ids ~= 1 or #stmts[1].expressions ~= 1 then
        return false
    end
    if stmts[1].expressions[1].kind ~= AstKind.StringExpression then
        return false
    end
    local validScope, validId = stmts[1].scope, stmts[1].ids[1]

    local hasSanityFor = false
    local hasTamperErr = false
    local ownedScopes = {}
    local mutatesExternal = false

    visitNode(stmt, function(n)
        if n.kind == AstKind.Block or n.kind == AstKind.ForStatement or n.kind == AstKind.ForInStatement then
            if n.scope then ownedScopes[n.scope] = true end
        end
    end)

    visitNode(stmt, function(n)
        if n.kind == AstKind.ForStatement then
            if n.initialValue.kind == AstKind.NumberExpression and n.initialValue.value == 0 then
                hasSanityFor = true
            end
        elseif n.kind == AstKind.StringExpression and n.value == "Tamper Detected!" then
            hasTamperErr = true
        elseif n.kind == AstKind.AssignmentVariable then
            if n.scope.isGlobal or not ownedScopes[n.scope] then
                local vname = n.scope:getVariableName(n.id)
                if vname ~= "l1" and vname ~= "l2" then
                    mutatesExternal = true
                end
            end
        elseif n.kind == AstKind.FunctionDeclaration and (n.scope.isGlobal or not ownedScopes[n.scope]) then
            mutatesExternal = true
        end
    end)

    local hasDoTrue = false
    for i = 2, #stmts do
        if stmts[i].kind == AstKind.DoStatement and #stmts[i].body.statements == 1 then
            local inner = stmts[i].body.statements[1]
            if inner.kind == AstKind.AssignmentStatement and #inner.lhs == 1 and #inner.rhs == 1 then
                if inner.lhs[1].kind == AstKind.AssignmentVariable
                    and inner.lhs[1].scope == validScope and inner.lhs[1].id == validId
                    and inner.rhs[1].kind == AstKind.BooleanExpression and inner.rhs[1].value == true then
                    hasDoTrue = true
                end
            end
        end
    end

    return hasSanityFor and hasTamperErr and hasDoTrue and not mutatesExternal
end

local function isTamperElseBlock(elseBlk)
    if not elseBlk or #elseBlk.statements == 0 then return false end
    local writesL1, writesL2, hasInfWhile = false, false, false
    visitNode(elseBlk, function(n)
        if n.kind == AstKind.WhileStatement and n.condition.kind == AstKind.BooleanExpression and n.condition.value == true then
            hasInfWhile = true
        elseif n.kind == AstKind.AssignmentVariable and n.scope and n.scope.isGlobal then
            local nm = n.scope:getVariableName(n.id)
            if nm == "l1" then writesL1 = true end
            if nm == "l2" then writesL2 = true end
        end
    end)
    return hasInfWhile and writesL1 and writesL2
end

local function isTamperErrFunction(fn)
    if fn.kind ~= AstKind.FunctionLiteralExpression or #fn.args ~= 0 then return false end
    local foundTamper = false
    visitNode(fn.body, function(n)
        if n.kind == AstKind.StringExpression and n.value == "Tamper Detected!" then
            foundTamper = true
        end
    end)
    return foundTamper
end

function Passes.removeAntiTamper(ast)
    local removed = false
    visitast(ast, function(node)
        if node.kind == AstKind.Block then
            local stmts = node.statements
            local i = 1
            while i <= #stmts do
                if isAntiTamperDoBlock(stmts[i]) then
                    table.remove(stmts, i)
                    removed = true
                elseif stmts[i].kind == AstKind.IfStatement
                    and #stmts[i].elseifs == 0
                    and stmts[i].elsebody
                    and isTamperElseBlock(stmts[i].elsebody) then
                    local ifIdx = i
                    local errIdx = nil
                    for k = ifIdx - 1, 1, -1 do
                        local sk = stmts[k]
                        if (sk.kind == AstKind.AssignmentStatement and #sk.rhs == 1 and isTamperErrFunction(sk.rhs[1]))
                            or (sk.kind == AstKind.LocalVariableDeclaration and #sk.expressions == 1 and isTamperErrFunction(sk.expressions[1])) then
                            errIdx = k
                            break
                        end
                    end

                    local startIdx = ifIdx
                    if errIdx then
                        startIdx = errIdx
                        local sanityCellSc, sanityCellId
                        for k = errIdx - 1, math.max(1, errIdx - 20), -1 do
                            local sk = stmts[k]
                            if sk.kind == AstKind.AssignmentStatement and #sk.lhs == 1 and #sk.rhs == 1 then
                                local r = sk.rhs[1]
                                if r.kind == AstKind.BooleanExpression and r.value == true then
                                    startIdx = k
                                    if sk.lhs[1].kind == AstKind.AssignmentIndexing
                                        and sk.lhs[1].base.kind == AstKind.VariableExpression then
                                        sanityCellSc, sanityCellId = sk.lhs[1].base.scope, sk.lhs[1].base.id
                                    end
                                    break
                                end
                            elseif sk.kind == AstKind.LocalVariableDeclaration and #sk.ids == 1 and #sk.expressions == 1 then
                                local r = sk.expressions[1]
                                if r.kind == AstKind.BooleanExpression and r.value == true then
                                    startIdx = k
                                    break
                                end
                            end
                        end

                        if sanityCellSc then
                            local wIdx = startIdx - 1
                            while wIdx >= 1
                                and stmts[wIdx].kind == AstKind.AssignmentStatement
                                and #stmts[wIdx].rhs == 1
                                and stmts[wIdx].rhs[1].kind == AstKind.NilExpression do
                                wIdx = wIdx - 1
                            end
                            if wIdx >= 1 and stmts[wIdx].kind == AstKind.WhileStatement then
                                for cIdx = wIdx - 1, math.max(1, wIdx - 20), -1 do
                                    local cs = stmts[cIdx]
                                    if cs.kind == AstKind.AssignmentStatement and #cs.lhs == 1 and #cs.rhs == 1
                                        and cs.lhs[1].kind == AstKind.AssignmentVariable
                                        and cs.lhs[1].scope == sanityCellSc and cs.lhs[1].id == sanityCellId
                                        and cs.rhs[1].kind == AstKind.TableConstructorExpression then
                                        startIdx = cIdx
                                        if cIdx >= 2 then
                                            local ps = stmts[cIdx - 1]
                                            if ps.kind == AstKind.AssignmentStatement and #ps.lhs == 1 and #ps.rhs == 1
                                                and ps.rhs[1].kind == AstKind.StringExpression then
                                                startIdx = cIdx - 1
                                            end
                                        end
                                        break
                                    end
                                end
                            end
                        end
                    end

                    local realBody = stmts[ifIdx].body.statements
                    local newStmts = {}
                    for k = 1, startIdx - 1 do
                        newStmts[#newStmts + 1] = stmts[k]
                    end
                    for k = 1, #realBody do
                        newStmts[#newStmts + 1] = realBody[k]
                    end
                    for k = ifIdx + 1, #stmts do
                        newStmts[#newStmts + 1] = stmts[k]
                    end
                    node.statements = newStmts
                    stmts = newStmts
                    removed = true
                    i = startIdx
                else
                    i = i + 1
                end
            end
        end
    end)
    return removed
end

local function matchWatermarkSetter(stmt)
    if stmt.kind ~= AstKind.PassSelfFunctionCallStatement then return nil end
    if stmt.passSelfFunctionName ~= "gsub" then return nil end
    if stmt.base.kind ~= AstKind.StringExpression or #stmt.base.value == 0 then return nil end
    if #stmt.args ~= 2 then return nil end
    if stmt.args[1].kind ~= AstKind.StringExpression or stmt.args[1].value ~= ".+" then return nil end
    local fn = stmt.args[2]
    if fn.kind ~= AstKind.FunctionLiteralExpression then return nil end
    if effectiveArgCount(fn.args) ~= 1 or fn.args[1].kind ~= AstKind.VariableExpression then return nil end
    if #fn.body.statements ~= 1 then return nil end
    local assign = fn.body.statements[1]
    if assign.kind ~= AstKind.AssignmentStatement or #assign.lhs ~= 1 or #assign.rhs ~= 1 then return nil end
    local lhs, rhs = assign.lhs[1], assign.rhs[1]
    if lhs.kind ~= AstKind.AssignmentVariable or not lhs.scope.isGlobal then return nil end
    if not isVarRef(rhs, fn.args[1].scope, fn.args[1].id) then return nil end
    return lhs.scope, lhs.id, stmt.base.value
end

local function matchWatermarkCheckIf(stmt, gScope, gId, content)
    if stmt.kind ~= AstKind.IfStatement then return false end
    if #stmt.elseifs > 0 or (stmt.elsebody and #stmt.elsebody.statements > 0) then return false end
    if #stmt.body.statements ~= 1 or stmt.body.statements[1].kind ~= AstKind.ReturnStatement then return false end
    if #stmt.body.statements[1].args ~= 0 then return false end
    local cond = stmt.condition
    if cond.kind ~= AstKind.NotEqualsExpression then return false end
    if isVarRef(cond.lhs, gScope, gId) and cond.rhs.kind == AstKind.StringExpression and cond.rhs.value == content then
        return true
    end
    if isVarRef(cond.rhs, gScope, gId) and cond.lhs.kind == AstKind.StringExpression and cond.lhs.value == content then
        return true
    end
    return false
end

function Passes.removeWatermarks(ast)
    local reads, writes = countVarUsage(ast)
    local removed = false
    local blocks = {}
    visitast(ast, function(n)
        if n.kind == AstKind.Block then blocks[#blocks + 1] = n end
    end)

    for _, blk in ipairs(blocks) do
        local stmts = blk.statements
        local i = 1
        while i <= #stmts do
            local gScope, gId, content = matchWatermarkSetter(stmts[i])
            if gScope then
                local k = varKey(gScope, gId)
                local checkBlock, checkStmt
                for _, b2 in ipairs(blocks) do
                    for _, s2 in ipairs(b2.statements) do
                        if s2 ~= stmts[i] and matchWatermarkCheckIf(s2, gScope, gId, content) then
                            checkBlock, checkStmt = b2, s2
                            break
                        end
                    end
                    if checkStmt then break end
                end
                local expectedReads = checkStmt and 1 or 0
                if (writes[k] or 0) == 1 and (reads[k] or 0) == expectedReads then
                    table.remove(stmts, i)
                    if checkBlock and checkStmt then
                        for j = 1, #checkBlock.statements do
                            if checkBlock.statements[j] == checkStmt then
                                table.remove(checkBlock.statements, j)
                                break
                            end
                        end
                    end
                    removed = true
                else
                    i = i + 1
                end
            else
                i = i + 1
            end
        end
    end
    return removed
end

local function matchSplitStringsCustomVariant(fn)
    if fn.kind ~= AstKind.FunctionLiteralExpression then return nil end
    if effectiveArgCount(fn.args) ~= 1 or fn.args[1].kind ~= AstKind.VariableExpression then return nil end
    local tblScope, tblId = fn.args[1].scope, fn.args[1].id
    local stmts = fn.body.statements
    if #stmts ~= 3 then return nil end
    if stmts[1].kind ~= AstKind.LocalVariableDeclaration then return nil end
    if stmts[2].kind ~= AstKind.ForStatement then return nil end
    if stmts[3].kind ~= AstKind.ReturnStatement or #stmts[3].args ~= 1 then return nil end

    local decl = stmts[1]
    local forStmt = stmts[2]
    local ret = stmts[3].args[1]

    if #decl.ids == 2 and #decl.expressions == 2 then
        local e1, e2 = decl.expressions[1], decl.expressions[2]
        if e1.kind == AstKind.IndexExpression and isVarRef(e1.base, tblScope, tblId)
            and e1.index.kind == AstKind.LenExpression and isVarRef(e1.index.rhs, tblScope, tblId)
            and e2.kind == AstKind.StringExpression and e2.value == ""
            and isVarRef(ret, decl.scope, decl.ids[2])
            and #forStmt.body.statements == 1 then
            return 1
        end
    elseif #decl.ids == 1 and #decl.expressions == 1 then
        local e1 = decl.expressions[1]
        if e1.kind == AstKind.StringExpression and e1.value == ""
            and isVarRef(ret, decl.scope, decl.ids[1])
            and forStmt.finalValue.kind == AstKind.DivExpression
            and forStmt.finalValue.lhs.kind == AstKind.LenExpression
            and isVarRef(forStmt.finalValue.lhs.rhs, tblScope, tblId)
            and forStmt.finalValue.rhs.kind == AstKind.NumberExpression
            and forStmt.finalValue.rhs.value == 2
            and #forStmt.body.statements == 1 then
            return 2
        end
    end
    return nil
end

local function evalSplitStringsCustom(variant, tableArg)
    if tableArg.kind ~= AstKind.TableConstructorExpression then return nil end
    local entries = tableArg.entries
    if variant == 1 then
        if #entries < 1 then return nil end
        local last = entries[#entries]
        if last.kind ~= AstKind.TableEntry or last.value.kind ~= AstKind.TableConstructorExpression then
            return nil
        end
        local strEntries = last.value.entries
        local count = #strEntries
        if #entries ~= count + 1 then return nil end
        local strs = {}
        for i = 1, count do
            if strEntries[i].kind ~= AstKind.TableEntry or strEntries[i].value.kind ~= AstKind.StringExpression then
                return nil
            end
            strs[i] = strEntries[i].value.value
        end
        local out = {}
        for i = 1, count do
            if entries[i].kind ~= AstKind.TableEntry or entries[i].value.kind ~= AstKind.NumberExpression then
                return nil
            end
            local idx = entries[i].value.value
            if type(idx) ~= "number" or not strs[idx] then return nil end
            out[i] = strs[idx]
        end
        return table.concat(out)
    elseif variant == 2 then
        if #entries % 2 ~= 0 then return nil end
        local half = #entries / 2
        local out = {}
        for i = 1, half do
            if entries[i].kind ~= AstKind.TableEntry or entries[i].value.kind ~= AstKind.NumberExpression then
                return nil
            end
            local idx = entries[i].value.value
            local strSlot = entries[half + idx]
            if not strSlot or strSlot.kind ~= AstKind.TableEntry or strSlot.value.kind ~= AstKind.StringExpression then
                return nil
            end
            out[i] = strSlot.value.value
        end
        return table.concat(out)
    end
    return nil
end

function Passes.unsplitStrings(ast)
    local changed = Passes.foldConstants(ast)
    local _, writes = countVarUsage(ast)

    local customHelpers = {}
    local concatHelpers = {}
    local tableGlobalWritten = false

    visitast(ast, function(node)
        if (node.kind == AstKind.AssignmentVariable or node.kind == AstKind.FunctionDeclaration)
            and node.scope.isGlobal and node.scope:getVariableName(node.id) == "table" then
            if node.kind == AstKind.AssignmentVariable or not node.indices or #node.indices == 0 then
                tableGlobalWritten = true
            end
        end
    end)

    visitast(ast, function(node)
        if node.kind == AstKind.LocalVariableDeclaration and #node.ids == 1 and #node.expressions == 1 then
            local k = varKey(node.scope, node.ids[1])
            if (writes[k] or 0) == 1 then
                local expr = node.expressions[1]
                local variant = matchSplitStringsCustomVariant(expr)
                if variant then
                    customHelpers[k] = { variant = variant, decl = node }
                elseif not tableGlobalWritten and expr.kind == AstKind.IndexExpression
                    and expr.base.kind == AstKind.VariableExpression and expr.base.scope.isGlobal
                    and expr.base.scope:getVariableName(expr.base.id) == "table"
                    and expr.index.kind == AstKind.StringExpression and expr.index.value == "concat" then
                    concatHelpers[k] = { decl = node }
                end
            end
        end
    end)

    visitast(ast, nil, function(node)
        if node.kind ~= AstKind.FunctionCallExpression or #node.args ~= 1 then return end
        local arg = node.args[1]
        if node.base.kind == AstKind.FunctionLiteralExpression then
            local variant = matchSplitStringsCustomVariant(node.base)
            if variant then
                local decoded = evalSplitStringsCustom(variant, arg)
                if decoded ~= nil then
                    changed = true
                    return Ast.StringExpression(decoded)
                end
            end
        elseif node.base.kind == AstKind.VariableExpression then
            local k = varKey(node.base.scope, node.base.id)
            local helper = customHelpers[k]
            if helper then
                local decoded = evalSplitStringsCustom(helper.variant, arg)
                if decoded ~= nil then
                    changed = true
                    return Ast.StringExpression(decoded)
                end
            end
            local tc = concatHelpers[k]
            if tc and arg.kind == AstKind.TableConstructorExpression then
                local parts = {}
                local ok = true
                for i = 1, #arg.entries do
                    local e = arg.entries[i]
                    if e.kind ~= AstKind.TableEntry or e.value.kind ~= AstKind.StringExpression then
                        ok = false
                        break
                    end
                    parts[i] = e.value.value
                end
                if ok then
                    changed = true
                    return Ast.StringExpression(table.concat(parts))
                end
            end
        end
    end)

    if changed then
        local postReads = countVarUsage(ast)
        visitast(ast, function(node)
            if node.kind == AstKind.Block then
                local stmts = node.statements
                local i = 1
                while i <= #stmts do
                    local s = stmts[i]
                    local removeStmt = false
                    if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 then
                        local k = varKey(s.scope, s.ids[1])
                        if (customHelpers[k] or concatHelpers[k]) and (postReads[k] or 0) == 0 then
                            removeStmt = true
                        end
                    end
                    if removeStmt then
                        table.remove(stmts, i)
                    else
                        i = i + 1
                    end
                end
            end
        end)
        Passes.foldConstants(ast)
    end

    return changed
end

local function decodeBase64(data, lookup)
    local length = #data
    local parts = {}
    local outIdx = 1
    for idx = 1, length, 4 do
        local c1 = string.sub(data, idx, idx)
        local c2 = string.sub(data, idx + 1, idx + 1)
        local c3 = string.sub(data, idx + 2, idx + 2)
        local c4 = string.sub(data, idx + 3, idx + 3)
        local n1 = lookup[c1]
        local n2 = lookup[c2]
        local n3 = lookup[c3]
        local n4 = lookup[c4]
        if n1 and n2 then
            local b1 = n1 * 4 + math.floor(n2 / 16)
            parts[outIdx] = string.char(b1)
            outIdx = outIdx + 1
            if n3 then
                local b2 = (n2 % 16) * 16 + math.floor(n3 / 4)
                parts[outIdx] = string.char(b2)
                outIdx = outIdx + 1
                if n4 then
                    local b3 = (n3 % 4) * 64 + n4
                    parts[outIdx] = string.char(b3)
                    outIdx = outIdx + 1
                end
            end
        end
    end
    return table.concat(parts)
end

local function decodeBase85(data, lookup)
    local length = #data
    local parts = {}
    local index = 1
    while index <= length do
        local remain = length - index + 1
        local count = remain >= 5 and 5 or remain
        local value = 0
        local valid = count > 1
        for j = 0, 4 do
            local code
            if j < count then
                local ch = string.sub(data, index + j, index + j)
                code = lookup[ch]
                if not code then
                    valid = false
                    break
                end
            else
                code = 84
            end
            value = value * 85 + code
        end
        if valid then
            local b1 = math.floor(value / 16777216) % 256
            local b2 = math.floor(value / 65536) % 256
            local b3 = math.floor(value / 256) % 256
            local b4 = value % 256
            if count == 5 then
                parts[#parts + 1] = string.char(b1, b2, b3, b4)
            elseif count == 4 then
                parts[#parts + 1] = string.char(b1, b2, b3)
            elseif count == 3 then
                parts[#parts + 1] = string.char(b1, b2)
            elseif count == 2 then
                parts[#parts + 1] = string.char(b1)
            end
        end
        index = index + count
    end
    return table.concat(parts)
end

local function parseLookupTable(expr)
    if expr.kind ~= AstKind.TableConstructorExpression then return nil end
    local n = #expr.entries
    if n ~= 64 and n ~= 85 then return nil end
    local tbl = {}
    local count = 0
    for i = 1, n do
        local e = expr.entries[i]
        if e.kind ~= AstKind.KeyedTableEntry
            or e.key.kind ~= AstKind.StringExpression or #e.key.value ~= 1
            or e.value.kind ~= AstKind.NumberExpression then
            return nil
        end
        tbl[e.key.value] = e.value.value
        count = count + 1
    end
    if count ~= n then return nil end
    return tbl, n
end

local function parseOffsetIndexing(expr, arrScope, arrId, argScope, argId)
    if expr.kind ~= AstKind.IndexExpression then return nil end
    if not isVarRef(expr.base, arrScope, arrId) then return nil end
    local idx = expr.index
    if isVarRef(idx, argScope, argId) then
        return 0
    end
    if idx.kind == AstKind.AddExpression then
        if isVarRef(idx.lhs, argScope, argId) and idx.rhs.kind == AstKind.NumberExpression then
            return idx.rhs.value
        end
        if isVarRef(idx.rhs, argScope, argId) and idx.lhs.kind == AstKind.NumberExpression then
            return idx.lhs.value
        end
    elseif idx.kind == AstKind.SubExpression then
        if isVarRef(idx.lhs, argScope, argId) and idx.rhs.kind == AstKind.NumberExpression then
            return -idx.rhs.value
        end
    end
    return nil
end

local function matchRotateStatement(stmt, arrScope, arrId)
    if stmt.kind ~= AstKind.ForInStatement or #stmt.expressions ~= 1 then return nil end
    local call = stmt.expressions[1]
    if call.kind ~= AstKind.FunctionCallExpression or #call.args ~= 1 then return nil end
    if call.base.kind ~= AstKind.VariableExpression or not call.base.scope.isGlobal then return nil end
    if call.base.scope:getVariableName(call.base.id) ~= "ipairs" then return nil end
    local outerTbl = call.args[1]
    if outerTbl.kind ~= AstKind.TableConstructorExpression or #outerTbl.entries ~= 3 then return nil end
    local ranges = {}
    for i = 1, 3 do
        local e = outerTbl.entries[i]
        if e.kind ~= AstKind.TableEntry or e.value.kind ~= AstKind.TableConstructorExpression or #e.value.entries ~= 2 then
            return nil
        end
        local a, b = e.value.entries[1], e.value.entries[2]
        if a.kind ~= AstKind.TableEntry or b.kind ~= AstKind.TableEntry
            or a.value.kind ~= AstKind.NumberExpression or b.value.kind ~= AstKind.NumberExpression then
            return nil
        end
        ranges[i] = { a.value.value, b.value.value }
    end
    local touchesArr = false
    visitNode(stmt.body, function(n)
        if n.kind == AstKind.AssignmentIndexing and isVarRef(n.base, arrScope, arrId) then
            touchesArr = true
        end
    end)
    if not touchesArr then return nil end
    return ranges
end

local function matchDecodeDoStatement(stmt, arrScope, arrId)
    if stmt.kind ~= AstKind.DoStatement then return nil end
    local refsArr = false
    local lookup64, lookup64Scope, lookup64Id
    local lookup85, lookup85Scope, lookup85Id

    for _, s in ipairs(stmt.body.statements) do
        if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 and #s.expressions == 1 then
            local e = s.expressions[1]
            if isVarRef(e, arrScope, arrId) then
                refsArr = true
            else
                local tbl, sz = parseLookupTable(e)
                if sz == 64 then
                    lookup64, lookup64Scope, lookup64Id = tbl, s.scope, s.ids[1]
                elseif sz == 85 then
                    lookup85, lookup85Scope, lookup85Id = tbl, s.scope, s.ids[1]
                end
            end
        end
    end
    if not refsArr or (not lookup64 and not lookup85) then
        return nil
    end

    if lookup64 and lookup85 then
        local prefix64, prefix85
        visitNode(stmt.body, function(n)
            if n.kind == AstKind.IfStatement and #n.elseifs == 1 then
                local function getEqStr(cond)
                    if cond.kind == AstKind.EqualsExpression then
                        if cond.rhs.kind == AstKind.StringExpression and #cond.rhs.value == 1 then
                            return cond.rhs.value
                        end
                        if cond.lhs.kind == AstKind.StringExpression and #cond.lhs.value == 1 then
                            return cond.lhs.value
                        end
                    end
                    return nil
                end
                local p1 = getEqStr(n.condition)
                local p2 = getEqStr(n.elseifs[1].condition)
                if p1 and p2 then
                    local b1Uses64 = false
                    visitNode(n.body, function(x)
                        if isVarRef(x, lookup64Scope, lookup64Id) then b1Uses64 = true end
                    end)
                    if b1Uses64 then
                        prefix64, prefix85 = p1, p2
                    else
                        prefix85, prefix64 = p1, p2
                    end
                end
            end
        end)
        if not prefix64 or not prefix85 then return nil end
        return { mode = "mixed", lookup64 = lookup64, lookup85 = lookup85, prefix64 = prefix64, prefix85 = prefix85 }
    elseif lookup64 then
        return { mode = "base64", lookup64 = lookup64 }
    else
        return { mode = "base85", lookup85 = lookup85 }
    end
end

local function matchLocalWrapperTable(stmt, wrapperScope, wrapperId)
    if stmt.kind ~= AstKind.LocalVariableDeclaration or #stmt.ids ~= 1 or #stmt.expressions ~= 1 then
        return nil
    end
    local tbl = stmt.expressions[1]
    if tbl.kind ~= AstKind.TableConstructorExpression or #tbl.entries == 0 then
        return nil
    end
    local methods = {}
    for i = 1, #tbl.entries do
        local e = tbl.entries[i]
        if e.kind ~= AstKind.KeyedTableEntry or e.key.kind ~= AstKind.StringExpression then
            return nil
        end
        local fn = e.value
        if fn.kind ~= AstKind.FunctionLiteralExpression or #fn.args < 1 or #fn.body.statements ~= 1 then
            return nil
        end
        local ret = fn.body.statements[1]
        if ret.kind ~= AstKind.ReturnStatement or #ret.args ~= 1 then
            return nil
        end
        local call = ret.args[1]
        if call.kind ~= AstKind.FunctionCallExpression or not isVarRef(call.base, wrapperScope, wrapperId) or #call.args ~= 1 then
            return nil
        end
        local argExpr = call.args[1]
        local matchedArgPos, localDelta
        for pos = 1, #fn.args do
            local a = fn.args[pos]
            if a.kind == AstKind.VariableExpression then
                if isVarRef(argExpr, a.scope, a.id) then
                    matchedArgPos, localDelta = pos, 0
                    break
                elseif argExpr.kind == AstKind.AddExpression then
                    if isVarRef(argExpr.lhs, a.scope, a.id) and argExpr.rhs.kind == AstKind.NumberExpression then
                        matchedArgPos, localDelta = pos, argExpr.rhs.value
                        break
                    elseif isVarRef(argExpr.rhs, a.scope, a.id) and argExpr.lhs.kind == AstKind.NumberExpression then
                        matchedArgPos, localDelta = pos, argExpr.lhs.value
                        break
                    end
                elseif argExpr.kind == AstKind.SubExpression then
                    if isVarRef(argExpr.lhs, a.scope, a.id) and argExpr.rhs.kind == AstKind.NumberExpression then
                        matchedArgPos, localDelta = pos, -argExpr.rhs.value
                        break
                    end
                end
            end
        end
        if not matchedArgPos then return nil end
        methods[e.key.value] = { argPos = matchedArgPos, delta = localDelta, argCount = #fn.args }
    end
    return methods
end

local function parseRotateRangesTable(outerTbl)
    if outerTbl.kind == AstKind.TableConstructorExpression and #outerTbl.entries == 1
        and outerTbl.entries[1].kind == AstKind.TableEntry
        and outerTbl.entries[1].value.kind == AstKind.FunctionCallExpression
        and #outerTbl.entries[1].value.args == 1 then
        outerTbl = outerTbl.entries[1].value.args[1]
    elseif outerTbl.kind == AstKind.FunctionCallExpression and #outerTbl.args == 1 then
        outerTbl = outerTbl.args[1]
    end
    if outerTbl.kind ~= AstKind.TableConstructorExpression or #outerTbl.entries ~= 3 then return nil end
    local ranges = {}
    for i = 1, 3 do
        local e = outerTbl.entries[i]
        if e.kind ~= AstKind.TableEntry or e.value.kind ~= AstKind.TableConstructorExpression or #e.value.entries ~= 2 then
            return nil
        end
        local a, b = e.value.entries[1], e.value.entries[2]
        if a.kind ~= AstKind.TableEntry or b.kind ~= AstKind.TableEntry
            or a.value.kind ~= AstKind.NumberExpression or b.value.kind ~= AstKind.NumberExpression then
            return nil
        end
        ranges[i] = { a.value.value, b.value.value }
    end
    if ranges[1][1] ~= 1 or ranges[2][1] ~= 1 then return nil end
    if ranges[3][1] ~= ranges[2][2] + 1 or ranges[3][2] ~= ranges[1][2] then return nil end
    return ranges
end

function Passes.resolveConstantArray(ast)
    local anyChanged = false
    local blocks = {}
    visitast(ast, function(n)
        if n.kind == AstKind.Block then blocks[#blocks + 1] = n end
    end)

    for _, blockNode in ipairs(blocks) do
        local stmts = blockNode.statements
        if #stmts >= 2 then
            local arrStmtIdx, arrScope, arrId, rawValues
            local wrapperStmtIdx, wrapperScope, wrapperId, wrapperDelta

            for idx = 1, #stmts do
                local s = stmts[idx]
                local candScope, candId, candTbl
                if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 and #s.expressions == 1
                    and s.expressions[1].kind == AstKind.TableConstructorExpression then
                    candScope, candId, candTbl = s.scope, s.ids[1], s.expressions[1]
                elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                    and s.lhs[1].kind == AstKind.AssignmentVariable and not s.lhs[1].scope.isGlobal
                    and s.rhs[1].kind == AstKind.TableConstructorExpression then
                    candScope, candId, candTbl = s.lhs[1].scope, s.lhs[1].id, s.rhs[1]
                end

                if candTbl then
                    local entries = candTbl.entries
                    if #entries > 0 then
                        local vals = {}
                        local hasNil = {}
                        local ok = true
                        for j = 1, #entries do
                            if entries[j].kind ~= AstKind.TableEntry or not isConstantLiteral(entries[j].value) then
                                ok = false
                                break
                            end
                            if entries[j].value.kind == AstKind.NilExpression then
                                hasNil[j] = true
                            else
                                vals[j] = entries[j].value.value
                            end
                        end
                        if ok then
                            for wIdx = idx + 1, #stmts do
                                local ws = stmts[wIdx]
                                if ws.kind == AstKind.AssignmentStatement and #ws.lhs == 1 and #ws.rhs == 1
                                    and ws.lhs[1].kind == AstKind.AssignmentVariable and not ws.lhs[1].scope.isGlobal
                                    and isVarRef(ws.rhs[1], candScope, candId) then
                                    candScope, candId = ws.lhs[1].scope, ws.lhs[1].id
                                end
                                local wScope, wId, wFn
                                if ws.kind == AstKind.LocalFunctionDeclaration then
                                    wScope, wId, wFn = ws.scope, ws.id, ws
                                elseif ws.kind == AstKind.LocalVariableDeclaration and #ws.ids == 1 and #ws.expressions == 1
                                    and ws.expressions[1].kind == AstKind.FunctionLiteralExpression then
                                    wScope, wId, wFn = ws.scope, ws.ids[1], ws.expressions[1]
                                elseif ws.kind == AstKind.AssignmentStatement and #ws.lhs == 1 and #ws.rhs == 1
                                    and ws.lhs[1].kind == AstKind.AssignmentVariable and not ws.lhs[1].scope.isGlobal
                                    and ws.rhs[1].kind == AstKind.FunctionLiteralExpression then
                                    wScope, wId, wFn = ws.lhs[1].scope, ws.lhs[1].id, ws.rhs[1]
                                end

                                if wFn and effectiveArgCount(wFn.args) == 1
                                    and wFn.args[1].kind == AstKind.VariableExpression
                                    and #wFn.body.statements == 1
                                    and wFn.body.statements[1].kind == AstKind.ReturnStatement
                                    and #wFn.body.statements[1].args == 1 then
                                    local delta = parseOffsetIndexing(
                                        wFn.body.statements[1].args[1],
                                        candScope, candId,
                                        wFn.args[1].scope, wFn.args[1].id
                                    )
                                    if delta ~= nil then
                                        arrStmtIdx, arrScope, arrId = idx, candScope, candId
                                        rawValues = { vals = vals, hasNil = hasNil, len = #entries }
                                        wrapperStmtIdx, wrapperScope, wrapperId, wrapperDelta = wIdx, wScope, wId, delta
                                        break
                                    end
                                end
                            end
                        end
                    end
                end
                if arrStmtIdx then break end
            end

            if arrStmtIdx then
                local rotateStmtIdx, rotateRanges
                local decodeStmtIdx, decodeInfo
                local extraSetupSpanEnd = nil

                for idx = arrStmtIdx + 1, #stmts do
                    if idx ~= wrapperStmtIdx then
                        if not rotateStmtIdx then
                            local r = matchRotateStatement(stmts[idx], arrScope, arrId)
                            if r then rotateStmtIdx, rotateRanges = idx, r end
                        end
                        if not decodeStmtIdx then
                            local d = matchDecodeDoStatement(stmts[idx], arrScope, arrId)
                            if d then decodeStmtIdx, decodeInfo = idx, d end
                        end
                    end
                end

                if not rotateRanges then
                    for idx = arrStmtIdx + 1, #stmts do
                        local st = stmts[idx]
                        local tblExpr
                        if st.kind == AstKind.LocalVariableDeclaration and #st.ids == 1 and #st.expressions == 1 then
                            tblExpr = st.expressions[1]
                        elseif st.kind == AstKind.AssignmentStatement and #st.lhs == 1 and #st.rhs == 1 then
                            tblExpr = st.rhs[1]
                        end
                        if tblExpr then
                            local rr = parseRotateRangesTable(tblExpr)
                            if rr and rr[1][2] == rawValues.len then
                                for wIdx = idx + 1, math.min(#stmts, idx + 15) do
                                    if stmts[wIdx].kind == AstKind.WhileStatement then
                                        local touchesArr = false
                                        visitNode(stmts[wIdx].body, function(n)
                                            if (n.kind == AstKind.AssignmentIndexing and isVarRef(n.base, arrScope, arrId))
                                                or isVarRef(n, arrScope, arrId) then
                                                touchesArr = true
                                            end
                                        end)
                                        if touchesArr then
                                            rotateRanges = rr
                                            extraSetupSpanEnd = math.max(extraSetupSpanEnd or 0, wIdx)
                                            break
                                        end
                                    end
                                end
                                if rotateRanges then break end
                            end
                        end
                    end
                end

                if not decodeInfo then
                    local lookup64, lookup64Scope, lookup64Id, l64Idx
                    local lookup85, lookup85Scope, lookup85Id, l85Idx
                    for idx = arrStmtIdx + 1, #stmts do
                        local st = stmts[idx]
                        local vSc, vId, vEx
                        if st.kind == AstKind.LocalVariableDeclaration and #st.ids == 1 and #st.expressions == 1 then
                            vSc, vId, vEx = st.scope, st.ids[1], st.expressions[1]
                        elseif st.kind == AstKind.AssignmentStatement and #st.lhs == 1 and #st.rhs == 1
                            and st.lhs[1].kind == AstKind.AssignmentVariable then
                            vSc, vId, vEx = st.lhs[1].scope, st.lhs[1].id, st.rhs[1]
                        end
                        if vEx and vEx.kind == AstKind.TableConstructorExpression then
                            local tbl, sz = parseLookupTable(vEx)
                            if sz == 64 and not lookup64 then
                                lookup64, lookup64Scope, lookup64Id, l64Idx = tbl, vSc, vId, idx
                            elseif sz == 85 and not lookup85 then
                                lookup85, lookup85Scope, lookup85Id, l85Idx = tbl, vSc, vId, idx
                            end
                        end
                    end

                    if lookup64 or lookup85 then
                        local searchFrom = math.max(l64Idx or 0, l85Idx or 0) + 1
                        for wIdx = searchFrom, math.min(#stmts, searchFrom + 20) do
                            if stmts[wIdx].kind == AstKind.WhileStatement then
                                local touchesArr = false
                                visitNode(stmts[wIdx].body, function(n)
                                    if n.kind == AstKind.AssignmentIndexing then
                                        touchesArr = true
                                    end
                                end)
                                if touchesArr then
                                    if lookup64 and lookup85 then
                                        local prefix64, prefix85
                                        local function getEqStr1(cond)
                                            if cond.kind == AstKind.EqualsExpression then
                                                if cond.rhs.kind == AstKind.StringExpression and #cond.rhs.value == 1 then
                                                    return cond.rhs.value
                                                end
                                                if cond.lhs.kind == AstKind.StringExpression and #cond.lhs.value == 1 then
                                                    return cond.lhs.value
                                                end
                                            end
                                            return nil
                                        end
                                        local function inspectArm(cond, armBody)
                                            local ch = getEqStr1(cond)
                                            if not ch then return end
                                            local u64, u85 = false, false
                                            visitNode(armBody, function(x)
                                                if isVarRef(x, lookup64Scope, lookup64Id) then u64 = true end
                                                if isVarRef(x, lookup85Scope, lookup85Id) then u85 = true end
                                            end)
                                            if u64 and not u85 then prefix64 = prefix64 or ch end
                                            if u85 and not u64 then prefix85 = prefix85 or ch end
                                        end
                                        visitNode(stmts[wIdx].body, function(n)
                                            if n.kind == AstKind.IfStatement then
                                                inspectArm(n.condition, n.body)
                                                for _, eif in ipairs(n.elseifs) do
                                                    inspectArm(eif.condition, eif.body)
                                                end
                                            end
                                        end)
                                        if prefix64 and prefix85 then
                                            decodeInfo = { mode = "mixed", lookup64 = lookup64, lookup85 = lookup85, prefix64 = prefix64, prefix85 = prefix85 }
                                            extraSetupSpanEnd = math.max(extraSetupSpanEnd or 0, wIdx)
                                        end
                                    elseif lookup64 then
                                        decodeInfo = { mode = "base64", lookup64 = lookup64 }
                                        extraSetupSpanEnd = math.max(extraSetupSpanEnd or 0, wIdx)
                                    else
                                        decodeInfo = { mode = "base85", lookup85 = lookup85 }
                                        extraSetupSpanEnd = math.max(extraSetupSpanEnd or 0, wIdx)
                                    end
                                    break
                                end
                            end
                        end
                    end
                end

                local len = rawValues.len
                local slots = {}
                for i = 1, len do
                    slots[i] = { isNil = rawValues.hasNil[i] or false, val = rawValues.vals[i] }
                end

                if rotateRanges then
                    for r = 1, #rotateRanges do
                        local lo, hi = rotateRanges[r][1], rotateRanges[r][2]
                        while lo < hi do
                            slots[lo], slots[hi] = slots[hi], slots[lo]
                            lo = lo + 1
                            hi = hi - 1
                        end
                    end
                end

                if decodeInfo then
                    for i = 1, len do
                        if not slots[i].isNil and type(slots[i].val) == "string" then
                            local data = slots[i].val
                            if decodeInfo.mode == "base64" then
                                slots[i].val = decodeBase64(data, decodeInfo.lookup64)
                            elseif decodeInfo.mode == "base85" then
                                slots[i].val = decodeBase85(data, decodeInfo.lookup85)
                            elseif decodeInfo.mode == "mixed" then
                                local p = string.sub(data, 1, 1)
                                local rest = string.sub(data, 2)
                                if p == decodeInfo.prefix64 then
                                    slots[i].val = decodeBase64(rest, decodeInfo.lookup64)
                                elseif p == decodeInfo.prefix85 then
                                    slots[i].val = decodeBase85(rest, decodeInfo.lookup85)
                                end
                            end
                        end
                    end
                end

                local localWrappers = {}
                visitNode(blockNode, function(subBlock)
                    if subBlock.kind == AstKind.Block then
                        for _, s in ipairs(subBlock.statements) do
                            local methods = matchLocalWrapperTable(s, wrapperScope, wrapperId)
                            if methods then
                                localWrappers[varKey(s.scope, s.ids[1])] = { methods = methods, stmt = s }
                            end
                        end
                    end
                end, nil, ast.globalScope)

                local function lookupSlot(rawIndex)
                    if type(rawIndex) ~= "number" then return nil end
                    local slot = slots[rawIndex]
                    if not slot then return nil end
                    if slot.isNil then
                        return Ast.NilExpression()
                    end
                    return makeConstantNode(slot.val)
                end

                local replacedCount = 0
                visitNode(blockNode, nil, function(n)
                    if n.kind == AstKind.FunctionCallExpression then
                        if isVarRef(n.base, wrapperScope, wrapperId) and #n.args == 1 and n.args[1].kind == AstKind.NumberExpression then
                            local cnode = lookupSlot(n.args[1].value + wrapperDelta)
                            if cnode then
                                replacedCount = replacedCount + 1
                                return cnode
                            end
                        elseif n.base.kind == AstKind.IndexExpression and n.base.base.kind == AstKind.VariableExpression
                            and n.base.index.kind == AstKind.StringExpression then
                            local lw = localWrappers[varKey(n.base.base.scope, n.base.base.id)]
                            if lw then
                                local m = lw.methods[n.base.index.value]
                                if m and #n.args >= m.argPos then
                                    local allConst = true
                                    for a = 1, #n.args do
                                        if not isConstantLiteral(n.args[a]) then allConst = false break end
                                    end
                                    if allConst and n.args[m.argPos].kind == AstKind.NumberExpression then
                                        local cnode = lookupSlot(n.args[m.argPos].value + m.delta + wrapperDelta)
                                        if cnode then
                                            replacedCount = replacedCount + 1
                                            return cnode
                                        end
                                    end
                                end
                            end
                        end
                    end
                end, ast.globalScope)

                local subBlocks = {}
                visitNode(blockNode, function(sb)
                    if sb.kind == AstKind.Block then subBlocks[#subBlocks + 1] = sb end
                end, nil, ast.globalScope)

                local postReadsAfterLw = countVarUsage(ast)
                for _, subBlock in ipairs(subBlocks) do
                    local i = 1
                    while i <= #subBlock.statements do
                        local s = subBlock.statements[i]
                        if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 then
                            local k = varKey(s.scope, s.ids[1])
                            if localWrappers[k] and (postReadsAfterLw[k] or 0) == 0 then
                                table.remove(subBlock.statements, i)
                                anyChanged = true
                            else
                                i = i + 1
                            end
                        else
                            i = i + 1
                        end
                    end
                end

                local postReads = countVarUsage(ast)
                local wrapperKey = varKey(wrapperScope, wrapperId)
                if (postReads[wrapperKey] or 0) == 0 then
                    local toRemove = {}
                    toRemove[stmts[wrapperStmtIdx]] = true
                    if rotateStmtIdx then toRemove[stmts[rotateStmtIdx]] = true end
                    if decodeStmtIdx then toRemove[stmts[decodeStmtIdx]] = true end
                    if extraSetupSpanEnd then
                        for idx = arrStmtIdx, extraSetupSpanEnd do
                            toRemove[stmts[idx]] = true
                        end
                    end

                    local extArrRefs = 0
                    visitast(ast, function(n)
                        if toRemove[n] or n == stmts[arrStmtIdx] then
                            return nil, true
                        end
                        if (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable or n.kind == AstKind.FunctionDeclaration)
                            and n.scope == arrScope and n.id == arrId then
                            extArrRefs = extArrRefs + 1
                        end
                    end)
                    if extArrRefs == 0 then
                        toRemove[stmts[arrStmtIdx]] = true
                    end

                    local i = 1
                    while i <= #stmts do
                        if toRemove[stmts[i]] then
                            table.remove(stmts, i)
                            anyChanged = true
                        else
                            i = i + 1
                        end
                    end
                elseif replacedCount > 0 then
                    anyChanged = true
                end
            end
        end
    end

    return anyChanged
end

local function makeEncryptStringsDecryptor(paramMul45, paramAdd45, paramMul8, secretKey8)
    local floor = math.floor
    return function(str, seed)
        local prevValues = {}
        local state45 = seed % 35184372088832
        local state8 = seed % 255 + 2
        local function nextByte()
            if #prevValues == 0 then
                state45 = (state45 * paramMul45 + paramAdd45) % 35184372088832
                repeat
                    state8 = state8 * paramMul8 % 257
                until state8 ~= 1
                local r = state8 % 32
                local shift = 13 - (state8 - r) / 32
                local n = floor(state45 / 2 ^ shift) % 4294967296 / 2 ^ r
                local rnd = floor(n % 1 * 4294967296) + floor(n)
                local low16 = rnd % 65536
                local high16 = (rnd - low16) / 65536
                prevValues = {
                    low16 % 256,
                    (low16 - low16 % 256) / 256,
                    high16 % 256,
                    (high16 - high16 % 256) / 256,
                }
            end
            return table.remove(prevValues)
        end
        local prevVal = secretKey8
        local out = {}
        for i = 1, #str do
            prevVal = (string.byte(str, i) + nextByte() + prevVal) % 256
            out[i] = string.char(prevVal)
        end
        return table.concat(out)
    end
end

local function matchEncryptStringsDoBlock(stmt)
    if stmt.kind ~= AstKind.DoStatement then return nil end
    local decryptScope, decryptId
    local stringsScope, stringsId
    local paramMul45, paramAdd45, paramMul8, secretKey8

    for _, s in ipairs(stmt.body.statements) do
        if s.kind == AstKind.FunctionDeclaration and (not s.indices or #s.indices == 0) and effectiveArgCount(s.args) == 2 then
            decryptScope, decryptId = s.scope, s.id
            visitNode(s.body, function(ds)
                if ds.kind == AstKind.LocalVariableDeclaration and #ds.ids == 1 and #ds.expressions == 1
                    and ds.expressions[1].kind == AstKind.NumberExpression then
                    secretKey8 = ds.expressions[1].value
                end
            end)
        elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
            and s.lhs[1].kind == AstKind.AssignmentVariable
            and s.rhs[1].kind == AstKind.FunctionCallExpression then
            local call = s.rhs[1]
            if call.base.kind == AstKind.VariableExpression and #call.args == 2 then
                stringsScope, stringsId = s.lhs[1].scope, s.lhs[1].id
            end
        elseif s.kind == AstKind.LocalFunctionDeclaration and effectiveArgCount(s.args) == 0 then
            visitNode(s.body, function(n)
                if n.kind == AstKind.ModExpression and n.rhs.kind == AstKind.NumberExpression then
                    if n.rhs.value == 35184372088832 and n.lhs.kind == AstKind.AddExpression then
                        local add = n.lhs
                        if add.rhs.kind == AstKind.NumberExpression and add.lhs.kind == AstKind.MulExpression
                            and add.lhs.rhs.kind == AstKind.NumberExpression then
                            paramMul45 = add.lhs.rhs.value
                            paramAdd45 = add.rhs.value
                        end
                    elseif n.rhs.value == 257 and n.lhs.kind == AstKind.MulExpression
                        and n.lhs.rhs.kind == AstKind.NumberExpression then
                        paramMul8 = n.lhs.rhs.value
                    end
                end
            end)
        end
    end

    if decryptScope and stringsScope and paramMul45 and paramAdd45 and paramMul8 and secretKey8 then
        return {
            decryptScope = decryptScope,
            decryptId = decryptId,
            stringsScope = stringsScope,
            stringsId = stringsId,
            decrypt = makeEncryptStringsDecryptor(paramMul45, paramAdd45, paramMul8, secretKey8),
        }
    end
    return nil
end

local function extractPrngParamsFromZeroArgFn(fnBody)
    local pMul45, pAdd45, pMul8
    visitNode(fnBody, function(n)
        if n.kind == AstKind.ModExpression and n.rhs.kind == AstKind.NumberExpression then
            if n.rhs.value == 35184372088832 and n.lhs.kind == AstKind.AddExpression then
                local add = n.lhs
                if add.rhs.kind == AstKind.NumberExpression and add.lhs.kind == AstKind.MulExpression
                    and add.lhs.rhs.kind == AstKind.NumberExpression then
                    pMul45 = add.lhs.rhs.value
                    pAdd45 = add.rhs.value
                end
            elseif n.rhs.value == 257 and n.lhs.kind == AstKind.MulExpression
                and n.lhs.rhs.kind == AstKind.NumberExpression then
                pMul8 = n.lhs.rhs.value
            end
        end
    end)
    return pMul45, pAdd45, pMul8
end

local function extractSecretKey8FromDecryptFn(fnBody)
    local mod256Vars = {}
    visitNode(fnBody, function(n)
        if n.kind == AstKind.WhileStatement or n.kind == AstKind.ForStatement then
            visitNode(n.body, function(m)
                if m.kind == AstKind.AssignmentStatement and #m.lhs == 1 and #m.rhs == 1
                    and m.lhs[1].kind == AstKind.AssignmentVariable
                    and m.rhs[1].kind == AstKind.ModExpression
                    and m.rhs[1].rhs.kind == AstKind.NumberExpression
                    and m.rhs[1].rhs.value == 256 then
                    mod256Vars[varKey(m.lhs[1].scope, m.lhs[1].id)] = true
                end
            end)
            for _ = 1, 2 do
                visitNode(n.body, function(m)
                    if m.kind == AstKind.AssignmentStatement and #m.lhs == 1 and #m.rhs == 1
                        and m.lhs[1].kind == AstKind.AssignmentVariable
                        and m.rhs[1].kind == AstKind.VariableExpression
                        and mod256Vars[varKey(m.rhs[1].scope, m.rhs[1].id)] then
                        mod256Vars[varKey(m.lhs[1].scope, m.lhs[1].id)] = true
                    end
                end)
            end
        end
    end)
    local foundKey = nil
    visitNode(fnBody, function(ds)
        if ds.kind == AstKind.WhileStatement or ds.kind == AstKind.ForStatement then
            return nil, true
        end
        if ds.kind == AstKind.LocalVariableDeclaration and #ds.ids == 1 and #ds.expressions == 1
            and ds.expressions[1].kind == AstKind.NumberExpression then
            local v = ds.expressions[1].value
            if next(mod256Vars) == nil or mod256Vars[varKey(ds.scope, ds.ids[1])] then
                foundKey = v
            end
        elseif ds.kind == AstKind.AssignmentStatement and #ds.lhs == 1 and #ds.rhs == 1
            and ds.lhs[1].kind == AstKind.AssignmentVariable
            and ds.rhs[1].kind == AstKind.NumberExpression then
            if mod256Vars[varKey(ds.lhs[1].scope, ds.lhs[1].id)] then
                foundKey = ds.rhs[1].value
            end
        end
    end)
    return foundKey
end

local function matchFlatEncryptStringsInBlock(blockNode)
    local stmts = blockNode.statements
    local nextByteIdx, paramMul45, paramAdd45, paramMul8
    local stringsIdx, stringsScope, stringsId
    local decryptIdx, decryptScope, decryptId, secretKey8

    local tblVars = {}
    for idx, s in ipairs(stmts) do
        local fnNode, vSc, vId
        if s.kind == AstKind.LocalFunctionDeclaration then
            fnNode, vSc, vId = s, s.scope, s.id
        elseif s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 and #s.expressions == 1
            and s.expressions[1].kind == AstKind.FunctionLiteralExpression then
            fnNode, vSc, vId = s.expressions[1], s.scope, s.ids[1]
        elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
            and s.lhs[1].kind == AstKind.AssignmentVariable and not s.lhs[1].scope.isGlobal
            and s.rhs[1].kind == AstKind.FunctionLiteralExpression then
            fnNode, vSc, vId = s.rhs[1], s.lhs[1].scope, s.lhs[1].id
        end

        if fnNode then
            if effectiveArgCount(fnNode.args) == 0 and not nextByteIdx then
                local m45, a45, m8 = extractPrngParamsFromZeroArgFn(fnNode.body)
                if m45 and a45 and m8 then
                    nextByteIdx, paramMul45, paramAdd45, paramMul8 = idx, m45, a45, m8
                end
            elseif effectiveArgCount(fnNode.args) == 2 and nextByteIdx and not decryptIdx then
                local hasMod45 = false
                visitNode(fnNode.body, function(n)
                    if n.kind == AstKind.NumberExpression and n.value == 35184372088832 then
                        hasMod45 = true
                    end
                end)
                if hasMod45 then
                    local sk8 = extractSecretKey8FromDecryptFn(fnNode.body)
                    if sk8 ~= nil then
                        decryptIdx, decryptScope, decryptId, secretKey8 = idx, vSc, vId, sk8
                    end
                end
            end
        elseif nextByteIdx and not decryptIdx then
            local lhsSc, lhsId, rhsEx
            if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 and #s.expressions == 1 then
                lhsSc, lhsId, rhsEx = s.scope, s.ids[1], s.expressions[1]
            elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                and s.lhs[1].kind == AstKind.AssignmentVariable and not s.lhs[1].scope.isGlobal then
                lhsSc, lhsId, rhsEx = s.lhs[1].scope, s.lhs[1].id, s.rhs[1]
            end
            if rhsEx then
                if rhsEx.kind == AstKind.TableConstructorExpression then
                    tblVars[varKey(lhsSc, lhsId)] = rhsEx
                elseif not stringsIdx and rhsEx.kind == AstKind.FunctionCallExpression and #rhsEx.args == 2 then
                    local mtArg = rhsEx.args[2]
                    if mtArg.kind == AstKind.VariableExpression then
                        mtArg = tblVars[varKey(mtArg.scope, mtArg.id)] or mtArg
                    end
                    local hasIndexKey = false
                    if mtArg.kind == AstKind.TableConstructorExpression then
                        for _, ent in ipairs(mtArg.entries) do
                            if ent.kind == AstKind.KeyedTableEntry
                                and ent.key.kind == AstKind.StringExpression
                                and ent.key.value == "__index" then
                                hasIndexKey = true
                            end
                        end
                    end
                    if hasIndexKey then
                        stringsIdx, stringsScope, stringsId = idx, lhsSc, lhsId
                    end
                elseif stringsIdx and isVarRef(rhsEx, stringsScope, stringsId) then
                    stringsIdx, stringsScope, stringsId = idx, lhsSc, lhsId
                end
            end
        end
    end

    if nextByteIdx and stringsIdx and decryptIdx and paramMul45 and paramAdd45 and paramMul8 and secretKey8 ~= nil then
        local spanStart = nextByteIdx
        for k = nextByteIdx - 1, 1, -1 do
            local sk = stmts[k]
            if sk.kind == AstKind.RepeatStatement or sk.kind == AstKind.WhileStatement then
                spanStart = k
            elseif sk.kind == AstKind.AssignmentStatement or sk.kind == AstKind.LocalVariableDeclaration then
                local touches256 = false
                visitNode(sk, function(n)
                    if n.kind == AstKind.NumberExpression and n.value == 256 then
                        touches256 = true
                    end
                end)
                if touches256 then
                    spanStart = math.max(1, k - 12)
                    break
                end
            end
        end
        return {
            decryptScope = decryptScope,
            decryptId = decryptId,
            stringsScope = stringsScope,
            stringsId = stringsId,
            decrypt = makeEncryptStringsDecryptor(paramMul45, paramAdd45, paramMul8, secretKey8),
            flatSpanStart = spanStart,
            flatSpanEnd = math.max(nextByteIdx, stringsIdx, decryptIdx),
        }
    end
    return nil
end

local function unhoistVmStrings(ast)
    local changed = false
    local _, writes = countVarUsage(ast)
    local blocks = {}
    visitast(ast, function(n)
        if n.kind == AstKind.Block then blocks[#blocks + 1] = n end
    end)

    for _, blockNode in ipairs(blocks) do
        local dataTables = {}
        for sIdx, s in ipairs(blockNode.statements) do
            local dtScope, dtId, dtTbl
            if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 and #s.expressions == 1
                and s.expressions[1].kind == AstKind.TableConstructorExpression then
                dtScope, dtId, dtTbl = s.scope, s.ids[1], s.expressions[1]
            elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                and s.lhs[1].kind == AstKind.AssignmentVariable and not s.lhs[1].scope.isGlobal
                and s.rhs[1].kind == AstKind.TableConstructorExpression then
                dtScope, dtId, dtTbl = s.lhs[1].scope, s.lhs[1].id, s.rhs[1]
            end
            if dtTbl then
                local entries = dtTbl.entries
                if #entries > 0 then
                    local strs = {}
                    local ok = true
                    for i = 1, #entries do
                        if entries[i].kind ~= AstKind.TableEntry or entries[i].value.kind ~= AstKind.StringExpression then
                            ok = false
                            break
                        end
                        strs[i] = entries[i].value.value
                    end
                    if ok then
                        local k = varKey(dtScope, dtId)
                        if (writes[k] or 0) == 1 then
                            dataTables[k] = { strs = strs, stmt = s }
                        end
                        for mIdx = sIdx + 1, math.min(#blockNode.statements, sIdx + 30) do
                            local ms = blockNode.statements[mIdx]
                            if ms.kind == AstKind.AssignmentStatement and #ms.lhs == 1 and #ms.rhs == 1
                                and ms.lhs[1].kind == AstKind.AssignmentVariable and not ms.lhs[1].scope.isGlobal then
                                if isVarRef(ms.rhs[1], dtScope, dtId) then
                                    local mk = varKey(ms.lhs[1].scope, ms.lhs[1].id)
                                    if (writes[mk] or 0) == 1 then
                                        dataTables[mk] = { strs = strs, stmt = ms, tempKey = k, tempStmt = s }
                                    end
                                    break
                                elseif ms.rhs[1].kind ~= AstKind.NilExpression then
                                    break
                                end
                            else
                                break
                            end
                        end
                    end
                end
            end
        end

        if next(dataTables) ~= nil then
            local fns = {}
            visitNode(blockNode, function(fn)
                if fn.kind == AstKind.FunctionLiteralExpression then fns[#fns + 1] = fn end
            end, nil, ast.globalScope)

            local blockChanged = false
            for _, fn in ipairs(fns) do
                local fstmts = fn.body.statements
                if #fstmts >= 2 then
                    local s1, s2 = fstmts[1], fstmts[2]
                    if s1.kind == AstKind.LocalVariableDeclaration and #s1.ids == 1 and #s1.expressions == 1
                        and s1.expressions[1].kind == AstKind.VariableExpression then
                        local dt = dataTables[varKey(s1.expressions[1].scope, s1.expressions[1].id)]
                        if dt and (writes[varKey(s1.scope, s1.ids[1])] or 0) == 1
                            and s2.kind == AstKind.LocalVariableDeclaration
                            and #s2.ids == #dt.strs and #s2.expressions == #dt.strs then
                            local valMap = {}
                            local valid = true
                            for i = 1, #s2.ids do
                                local e = s2.expressions[i]
                                if e.kind ~= AstKind.IndexExpression
                                    or (not isVarRef(e.base, s1.scope, s1.ids[1])
                                        and not isVarRef(e.base, s1.expressions[1].scope, s1.expressions[1].id))
                                    or e.index.kind ~= AstKind.NumberExpression
                                    or e.index.value ~= i
                                    or (writes[varKey(s2.scope, s2.ids[i])] or 0) ~= 1 then
                                    valid = false
                                    break
                                end
                                valMap[varKey(s2.scope, s2.ids[i])] = dt.strs[i]
                            end
                            if valid then
                                table.remove(fstmts, 2)
                                table.remove(fstmts, 1)
                                visitNode(fn.body, nil, function(n)
                                    if n.kind == AstKind.VariableExpression then
                                        local str = valMap[varKey(n.scope, n.id)]
                                        if str ~= nil then
                                            return Ast.StringExpression(str)
                                        end
                                    end
                                end, ast.globalScope)
                                blockChanged = true
                                changed = true
                            end
                        end
                    end
                end
            end

            if blockChanged then
                for pass = 1, 2 do
                    local postReads = countVarUsage(ast)
                    local extraRemovals = {}
                    for _, dt in pairs(dataTables) do
                        if dt.tempKey and (postReads[dt.tempKey] or 0) == 0 and dt.tempStmt then
                            extraRemovals[dt.tempStmt] = true
                        end
                    end
                    local i = 1
                    while i <= #blockNode.statements do
                        local s = blockNode.statements[i]
                        local k = nil
                        if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 then
                            k = varKey(s.scope, s.ids[1])
                        elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and s.lhs[1].kind == AstKind.AssignmentVariable then
                            k = varKey(s.lhs[1].scope, s.lhs[1].id)
                        end
                        if extraRemovals[s] or (k and dataTables[k] and (postReads[k] or 0) == 0) then
                            table.remove(blockNode.statements, i)
                        else
                            i = i + 1
                        end
                    end
                end
            end
        end
    end

    return changed
end

function Passes.decryptStrings(ast)
    local anyChanged = false
    local blocks = {}
    visitast(ast, function(n)
        if n.kind == AstKind.Block then blocks[#blocks + 1] = n end
    end)

    for _, blockNode in ipairs(blocks) do
        local instances = {}
        for _, s in ipairs(blockNode.statements) do
            local info = matchEncryptStringsDoBlock(s)
            if info then
                info.doStmt = s
                instances[#instances + 1] = info
            end
        end
        if #instances == 0 then
            local flatInfo = matchFlatEncryptStringsInBlock(blockNode)
            if flatInfo then
                instances[#instances + 1] = flatInfo
            end
        end

        for _, inst in ipairs(instances) do
            local cache = {}
            local function evalDecryptCall(call)
                if call and call.kind == AstKind.FunctionCallExpression
                    and isVarRef(call.base, inst.decryptScope, inst.decryptId)
                    and #call.args == 2
                    and call.args[1].kind == AstKind.StringExpression
                    and call.args[2].kind == AstKind.NumberExpression then
                    local enc = call.args[1].value
                    local seed = call.args[2].value
                    if cache[seed] == nil then
                        cache[seed] = inst.decrypt(enc, seed)
                    end
                    return cache[seed]
                end
                return nil
            end

            visitast(ast, nil, function(n)
                if n.kind == AstKind.IndexExpression and isVarRef(n.base, inst.stringsScope, inst.stringsId) then
                    local dec = evalDecryptCall(n.index)
                    if dec ~= nil then
                        anyChanged = true
                        return Ast.StringExpression(dec)
                    end
                end
            end)

            visitast(ast, function(subBlk)
                if subBlk.kind ~= AstKind.Block then return end
                local bstmts = subBlk.statements
                local pendingDecVar = {}
                for idx = 1, #bstmts do
                    local st = bstmts[idx]
                    if st.kind == AstKind.AssignmentStatement and #st.lhs == 1 and #st.rhs == 1
                        and st.lhs[1].kind == AstKind.AssignmentVariable then
                        local k = varKey(st.lhs[1].scope, st.lhs[1].id)
                        local dec = evalDecryptCall(st.rhs[1])
                        if dec ~= nil then
                            pendingDecVar[k] = { str = dec, defIdx = idx, used = false }
                        else
                            if next(pendingDecVar) ~= nil then
                                st.rhs[1] = visitNode(st.rhs[1], nil, function(x)
                                    if x.kind == AstKind.IndexExpression and isVarRef(x.base, inst.stringsScope, inst.stringsId)
                                        and x.index.kind == AstKind.VariableExpression then
                                        local pk = varKey(x.index.scope, x.index.id)
                                        if pendingDecVar[pk] then
                                            pendingDecVar[pk].used = true
                                            anyChanged = true
                                            return Ast.StringExpression(pendingDecVar[pk].str)
                                        end
                                    end
                                end, ast.globalScope)
                            end
                            pendingDecVar[k] = nil
                        end
                    elseif next(pendingDecVar) ~= nil then
                        visitNode(st, nil, function(x)
                            if x.kind == AstKind.IndexExpression and isVarRef(x.base, inst.stringsScope, inst.stringsId)
                                and x.index.kind == AstKind.VariableExpression then
                                local pk = varKey(x.index.scope, x.index.id)
                                if pendingDecVar[pk] then
                                    pendingDecVar[pk].used = true
                                    anyChanged = true
                                    return Ast.StringExpression(pendingDecVar[pk].str)
                                end
                            end
                        end, ast.globalScope)
                        if st.kind == AstKind.WhileStatement or st.kind == AstKind.RepeatStatement
                            or st.kind == AstKind.ForStatement or st.kind == AstKind.ForInStatement then
                            pendingDecVar = {}
                        end
                    end
                end
                for _, infoP in pairs(pendingDecVar) do
                    if infoP.used then
                        local defSt = bstmts[infoP.defIdx]
                        defSt.rhs[1] = Ast.NilExpression()
                    end
                end
                for idx = 1, #bstmts do
                    local st = bstmts[idx]
                    if st.kind == AstKind.AssignmentStatement and #st.lhs == 1 and #st.rhs == 1
                        and st.lhs[1].kind == AstKind.AssignmentVariable then
                        local isEncRef = evalDecryptCall(st.rhs[1]) ~= nil
                            or isVarRef(st.rhs[1], inst.stringsScope, inst.stringsId)
                            or isVarRef(st.rhs[1], inst.decryptScope, inst.decryptId)
                        if isEncRef then
                            local vSc, vId = st.lhs[1].scope, st.lhs[1].id
                            local laterReads = 0
                            for j = idx + 1, #bstmts do
                                local sj = bstmts[j]
                                if sj.kind == AstKind.AssignmentStatement and #sj.lhs == 1
                                    and sj.lhs[1].kind == AstKind.AssignmentVariable
                                    and sj.lhs[1].scope == vSc and sj.lhs[1].id == vId then
                                    visitNode(sj.rhs[1], function(m)
                                        if isVarRef(m, vSc, vId) then laterReads = laterReads + 1 end
                                    end, nil, ast.globalScope)
                                    break
                                else
                                    visitNode(sj, function(m)
                                        if isVarRef(m, vSc, vId) then laterReads = laterReads + 1 end
                                    end, nil, ast.globalScope)
                                end
                            end
                            if laterReads == 0 then
                                st.rhs[1] = Ast.NilExpression()
                                anyChanged = true
                            end
                        end
                    end
                end
            end)

            if inst.doStmt then
                local extReads, extWrites = 0, 0
                visitast(ast, function(n)
                    if n == inst.doStmt then
                        return nil, true
                    end
                    if n.kind == AstKind.VariableExpression then
                        if (n.scope == inst.stringsScope and n.id == inst.stringsId)
                            or (n.scope == inst.decryptScope and n.id == inst.decryptId) then
                            extReads = extReads + 1
                        end
                    elseif n.kind == AstKind.AssignmentVariable or n.kind == AstKind.FunctionDeclaration then
                        if (n.scope == inst.stringsScope and n.id == inst.stringsId)
                            or (n.scope == inst.decryptScope and n.id == inst.decryptId) then
                            extWrites = extWrites + 1
                        end
                    end
                end)

                if extReads == 0 and extWrites == 0 then
                    local stmts = blockNode.statements
                    local i = 1
                    while i <= #stmts do
                        local s = stmts[i]
                        if s == inst.doStmt then
                            table.remove(stmts, i)
                            anyChanged = true
                        elseif s.kind == AstKind.LocalVariableDeclaration and (#s.expressions == 0) then
                            local kept = {}
                            for j = 1, #s.ids do
                                local id = s.ids[j]
                                if not ((s.scope == inst.stringsScope and id == inst.stringsId)
                                    or (s.scope == inst.decryptScope and id == inst.decryptId)) then
                                    kept[#kept + 1] = id
                                else
                                    anyChanged = true
                                end
                            end
                            if #kept == 0 then
                                table.remove(stmts, i)
                            else
                                s.ids = kept
                                i = i + 1
                            end
                        else
                            i = i + 1
                        end
                    end
                end
            elseif inst.flatSpanStart and inst.flatSpanEnd then
                local stmts = blockNode.statements
                local toSkip = {}
                for k = inst.flatSpanStart, inst.flatSpanEnd do
                    if stmts[k] then toSkip[stmts[k]] = true end
                end
                local extReads = 0
                visitast(ast, function(n)
                    if toSkip[n] then return nil, true end
                    if n.kind == AstKind.VariableExpression then
                        if (n.scope == inst.stringsScope and n.id == inst.stringsId)
                            or (n.scope == inst.decryptScope and n.id == inst.decryptId) then
                            extReads = extReads + 1
                        end
                    end
                end)
                if extReads == 0 then
                    local i = 1
                    while i <= #stmts do
                        if toSkip[stmts[i]] then
                            table.remove(stmts, i)
                            anyChanged = true
                        else
                            i = i + 1
                        end
                    end
                end
            end
        end
    end

    if unhoistVmStrings(ast) then
        anyChanged = true
    end

    return anyChanged
end

local METATABLE_OP_KINDS = {
    __add = AstKind.AddExpression,
    __sub = AstKind.SubExpression,
    __index = AstKind.IndexExpression,
    __mul = AstKind.MulExpression,
    __div = AstKind.DivExpression,
    __pow = AstKind.PowExpression,
    __concat = AstKind.StrCatExpression,
}

local function matchProxyCall(expr, setmtMap)
    if expr.kind ~= AstKind.FunctionCallExpression or #expr.args ~= 2 then return nil end
    if expr.base.kind ~= AstKind.VariableExpression then return nil end
    if not setmtMap[varKey(expr.base.scope, expr.base.id)] then return nil end
    local valTbl, mtTbl = expr.args[1], expr.args[2]
    if valTbl.kind ~= AstKind.TableConstructorExpression or #valTbl.entries ~= 1 then return nil end
    if mtTbl.kind ~= AstKind.TableConstructorExpression or #mtTbl.entries ~= 2 then return nil end
    local valEntry = valTbl.entries[1]
    if valEntry.kind ~= AstKind.KeyedTableEntry or valEntry.key.kind ~= AstKind.StringExpression then return nil end
    local valName = valEntry.key.value
    local initExpr = valEntry.value

    local setKind, getKind
    for i = 1, 2 do
        local me = mtTbl.entries[i]
        if me.kind ~= AstKind.KeyedTableEntry or me.key.kind ~= AstKind.StringExpression then return nil end
        local opKind = METATABLE_OP_KINDS[me.key.value]
        if not opKind or me.value.kind ~= AstKind.FunctionLiteralExpression or #me.value.args ~= 2 then return nil end
        if #me.value.body.statements ~= 1 then return nil end
        local s = me.value.body.statements[1]
        if s.kind == AstKind.AssignmentStatement then
            setKind = opKind
        elseif s.kind == AstKind.ReturnStatement then
            getKind = opKind
        else
            return nil
        end
    end
    if not setKind or not getKind then return nil end
    return {
        valName = valName,
        initExpr = initExpr,
        setKind = setKind,
        getKind = getKind,
    }
end

function Passes.unproxifyLocals(ast)
    local _, writes = countVarUsage(ast)
    local setmtVars = {}
    local emptyFnVars = {}

    visitast(ast, function(node)
        if node.kind == AstKind.LocalVariableDeclaration and #node.ids == 1 and #node.expressions == 1 then
            local k = varKey(node.scope, node.ids[1])
            if (writes[k] or 0) == 1 then
                local e = node.expressions[1]
                if e.kind == AstKind.VariableExpression and e.scope.isGlobal
                    and e.scope:getVariableName(e.id) == "setmetatable" then
                    setmtVars[k] = node
                elseif e.kind == AstKind.FunctionLiteralExpression and #e.body.statements == 0
                    and (#e.args == 0 or (#e.args == 1 and e.args[1].kind == AstKind.VarargExpression)) then
                    emptyFnVars[k] = node
                end
            end
        elseif node.kind == AstKind.LocalFunctionDeclaration and #node.body.statements == 0
            and (#node.args == 0 or (#node.args == 1 and node.args[1].kind == AstKind.VarargExpression)) then
            local k = varKey(node.scope, node.id)
            if (writes[k] or 0) == 1 then
                emptyFnVars[k] = node
            end
        end
    end)

    if next(setmtVars) == nil then
        return false
    end

    local proxies = {}
    visitast(ast, function(node)
        if node.kind == AstKind.LocalVariableDeclaration and node.expressions and #node.expressions > 0 then
            for i = 1, #node.ids do
                local expr = node.expressions[i]
                if expr then
                    local info = matchProxyCall(expr, setmtVars)
                    if info then
                        local k = varKey(node.scope, node.ids[i])
                        proxies[k] = info
                        if info.initExpr.kind == AstKind.FunctionLiteralExpression
                            and #info.initExpr.body.statements == 0
                            and (#info.initExpr.args == 0 or (#info.initExpr.args == 1 and info.initExpr.args[1].kind == AstKind.VarargExpression)) then
                            emptyFnVars[k] = node
                        end
                    end
                end
            end
        end
    end)

    if next(proxies) == nil then
        return false
    end

    local function isEmptyFnBase(baseExpr)
        if baseExpr.kind == AstKind.VariableExpression then
            return emptyFnVars[varKey(baseExpr.scope, baseExpr.id)] ~= nil
        end
        local b = baseExpr.lhs or baseExpr.base
        if b and b.kind == AstKind.VariableExpression then
            local k = varKey(b.scope, b.id)
            local info = proxies[k]
            if info and baseExpr.kind == info.getKind and emptyFnVars[k] then
                return true
            end
        end
        return false
    end

    visitast(ast, function(node)
        if node.kind == AstKind.LocalVariableDeclaration and node.expressions and #node.expressions > 0 then
            if #node.ids == 1 and #node.expressions == 1 then
                local info = proxies[varKey(node.scope, node.ids[1])]
                if info and info.initExpr.kind == AstKind.FunctionLiteralExpression then
                    return Ast.LocalFunctionDeclaration(node.scope, node.ids[1], info.initExpr.args, info.initExpr.body)
                end
            end
            for i = 1, #node.ids do
                local info = proxies[varKey(node.scope, node.ids[i])]
                if info then
                    node.expressions[i] = info.initExpr
                end
            end
            if #node.expressions > 0 then
                local allNil = true
                for j = 1, #node.expressions do
                    if node.expressions[j].kind ~= AstKind.NilExpression then
                        allNil = false
                        break
                    end
                end
                if allNil then
                    node.expressions = {}
                end
            end
            return node
        end

        if node.kind == AstKind.FunctionCallStatement and isEmptyFnBase(node.base) and #node.args >= 1 then
            local first = node.args[1]
            local baseVar = first.lhs or first.base
            local rhsVal = first.rhs or first.index
            if baseVar and baseVar.kind == AstKind.VariableExpression then
                local info = proxies[varKey(baseVar.scope, baseVar.id)]
                if info and first.kind == info.setKind then
                    local rhsList = { rhsVal }
                    for j = 2, #node.args do
                        rhsList[#rhsList + 1] = node.args[j]
                    end
                    return Ast.AssignmentStatement({ Ast.AssignmentVariable(baseVar.scope, baseVar.id) }, rhsList)
                end
            end
        end

        if node.kind == AstKind.AssignmentStatement then
            for i = 1, #node.lhs do
                local lhs = node.lhs[i]
                if lhs.kind == AstKind.AssignmentIndexing and lhs.base.kind == AstKind.VariableExpression
                    and lhs.index.kind == AstKind.StringExpression then
                    local info = proxies[varKey(lhs.base.scope, lhs.base.id)]
                    if info and lhs.index.value == info.valName then
                        node.lhs[i] = Ast.AssignmentVariable(lhs.base.scope, lhs.base.id)
                    end
                end
            end
            return node
        end

        if node.kind == AstKind.FunctionDeclaration and node.indices and #node.indices > 0 then
            local info = proxies[varKey(node.scope, node.id)]
            if info and node.indices[1] == info.valName then
                table.remove(node.indices, 1)
            end
            return node
        end

        local baseVar = node.lhs or node.base
        if baseVar and baseVar.kind == AstKind.VariableExpression then
            local info = proxies[varKey(baseVar.scope, baseVar.id)]
            if info and node.kind == info.getKind then
                return Ast.VariableExpression(baseVar.scope, baseVar.id), true
            end
        end
    end)

    local postReads = countVarUsage(ast)
    visitast(ast, function(node)
        if node.kind == AstKind.Block then
            local stmts = node.statements
            local i = 1
            while i <= #stmts do
                local s = stmts[i]
                if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1 then
                    local k = varKey(s.scope, s.ids[1])
                    if (setmtVars[k] or emptyFnVars[k]) and (postReads[k] or 0) == 0 then
                        table.remove(stmts, i)
                    else
                        i = i + 1
                    end
                elseif s.kind == AstKind.LocalFunctionDeclaration then
                    local k = varKey(s.scope, s.id)
                    if emptyFnVars[k] and (postReads[k] or 0) == 0 then
                        table.remove(stmts, i)
                    else
                        i = i + 1
                    end
                else
                    i = i + 1
                end
            end
        end
    end)

    return true
end

local FUNCTION_KINDS = lookupify({
    AstKind.FunctionDeclaration,
    AstKind.LocalFunctionDeclaration,
    AstKind.FunctionLiteralExpression,
})

local function functionBodyUsesVararg(body)
    local uses = false
    local function scan(node)
        if type(node) ~= "table" then return end
        if FUNCTION_KINDS[node.kind] then return end
        if node.kind == AstKind.VarargExpression then
            uses = true
            return
        end
        if node.kind == AstKind.VariableExpression and node.scope.isGlobal and node.scope:getVariableName(node.id) == "arg" then
            uses = true
            return
        end
        for k, v in pairs(node) do
            if k ~= "scope" and k ~= "parentScope" and type(v) == "table" then
                scan(v)
                if uses then return end
            end
        end
    end
    scan(body)
    return uses
end

function Passes.removeAddedVarargs(ast)
    local funcs = {}
    local allHaveVararg = true
    local usesDebugInfo = false

    visitast(ast, function(node)
        if FUNCTION_KINDS[node.kind] then
            funcs[#funcs + 1] = node
            if #node.args == 0 or node.args[#node.args].kind ~= AstKind.VarargExpression then
                allHaveVararg = false
            end
        elseif node.kind == AstKind.VariableExpression and node.scope.isGlobal then
            if node.scope:getVariableName(node.id) == "debug" then
                usesDebugInfo = true
            end
        end
    end)

    if #funcs == 0 or not allHaveVararg or usesDebugInfo then
        return false
    end

    local changed = false
    for i = 1, #funcs do
        local fn = funcs[i]
        if not functionBodyUsesVararg(fn.body) then
            table.remove(fn.args, #fn.args)
            changed = true
        end
    end
    return changed
end

local function cloneSimpleExpr(expr)
    if expr.kind == AstKind.StringExpression then
        return Ast.StringExpression(expr.value)
    elseif expr.kind == AstKind.NumberExpression then
        return Ast.NumberExpression(expr.value)
    elseif expr.kind == AstKind.BooleanExpression then
        return Ast.BooleanExpression(expr.value)
    elseif expr.kind == AstKind.VariableExpression then
        return Ast.VariableExpression(expr.scope, expr.id)
    end
    return nil
end

function Passes.simplifyCells(ast)
    local anyChanged = false

    local _, allWrites = countVarUsage(ast)
    visitast(ast, function(n)
        if n.kind == AstKind.ForStatement then
            local k = varKey(n.scope, n.id)
            allWrites[k] = (allWrites[k] or 0) + 2
        elseif n.kind == AstKind.ForInStatement then
            for _, id in ipairs(n.ids) do
                local k = varKey(n.scope, id)
                allWrites[k] = (allWrites[k] or 0) + 2
            end
        elseif n.lhs and n.rhs and n.kind ~= AstKind.AssignmentStatement then
            if n.lhs.kind == AstKind.AssignmentVariable then
                local k = varKey(n.lhs.scope, n.lhs.id)
                allWrites[k] = (allWrites[k] or 0) + 2
            end
        end
    end)

    local blocks = {}
    visitast(ast, function(n)
        if n.kind == AstKind.Block then blocks[#blocks + 1] = n end
    end)

    for _, blockNode in ipairs(blocks) do
        local stmts = blockNode.statements
        local newLocalIds = {}
        local idx = 1
        while idx <= #stmts do
            local st = stmts[idx]
            local cellSc, cellId, isLocalDecl
            if st.kind == AstKind.LocalVariableDeclaration and #st.ids == 1 and #st.expressions == 1
                and st.expressions[1].kind == AstKind.TableConstructorExpression
                and #st.expressions[1].entries == 0 then
                cellSc, cellId, isLocalDecl = st.scope, st.ids[1], true
            elseif st.kind == AstKind.AssignmentStatement and #st.lhs == 1 and #st.rhs == 1
                and st.lhs[1].kind == AstKind.AssignmentVariable and not st.lhs[1].scope.isGlobal
                and st.rhs[1].kind == AstKind.TableConstructorExpression
                and #st.rhs[1].entries == 0 then
                cellSc, cellId, isLocalDecl = st.lhs[1].scope, st.lhs[1].id, false
            end

            local unboxed = false
            if cellSc then
                local killIdx = nil
                local invalidCell = false
                for k = idx + 1, #stmts do
                    local sk = stmts[k]
                    if sk.kind == AstKind.AssignmentStatement then
                        local topWrote = false
                        for _, l in ipairs(sk.lhs) do
                            if l.kind == AstKind.AssignmentVariable and l.scope == cellSc and l.id == cellId then
                                topWrote = true
                            end
                        end
                        if topWrote then
                            killIdx = k
                            break
                        end
                    elseif sk.kind == AstKind.LocalVariableDeclaration and sk.scope == cellSc then
                        for _, id in ipairs(sk.ids) do
                            if id == cellId then
                                killIdx = k
                                break
                            end
                        end
                        if killIdx then break end
                    end
                    visitNode(sk, function(n)
                        if n.kind == AstKind.AssignmentVariable and n.scope == cellSc and n.id == cellId then
                            invalidCell = true
                        end
                    end, nil, ast.globalScope)
                    if invalidCell then break end
                end

                local rangeEnd = killIdx and (killIdx - 1) or #stmts
                if killIdx then
                    for _, r in ipairs(stmts[killIdx].rhs or {}) do
                        visitNode(r, function(n)
                            if isVarRef(n, cellSc, cellId) then invalidCell = true end
                        end, nil, ast.globalScope)
                    end
                end

                local snapDecls = {}
                local snapSet = {}
                local slotNilWriteIdxs = {}
                local slotValWriteIdx = nil
                local totalSlotReads = 0

                if not invalidCell then
                    local curNil = {}
                    for m = 1, idx do
                        local sm = stmts[m]
                        if sm.kind == AstKind.AssignmentStatement and #sm.lhs == 1 and #sm.rhs == 1
                            and sm.lhs[1].kind == AstKind.AssignmentVariable and not sm.lhs[1].scope.isGlobal then
                            local lk = varKey(sm.lhs[1].scope, sm.lhs[1].id)
                            if sm.rhs[1].kind == AstKind.NilExpression
                                or (sm.rhs[1].kind == AstKind.VariableExpression and curNil[varKey(sm.rhs[1].scope, sm.rhs[1].id)]) then
                                curNil[lk] = true
                            else
                                curNil[lk] = nil
                            end
                        elseif sm.kind == AstKind.LocalVariableDeclaration then
                            for idIdx = 1, #sm.ids do
                                local ex = sm.expressions and sm.expressions[idIdx]
                                local lk = varKey(sm.scope, sm.ids[idIdx])
                                if not ex or ex.kind == AstKind.NilExpression then
                                    curNil[lk] = true
                                else
                                    curNil[lk] = nil
                                end
                            end
                        else
                            visitNode(sm, function(n)
                                if n.kind == AstKind.AssignmentVariable then
                                    curNil[varKey(n.scope, n.id)] = nil
                                end
                            end, nil, ast.globalScope)
                        end
                    end

                    for k = idx + 1, rangeEnd do
                        local sk = stmts[k]
                        local isTopSlotWrite = false
                        if sk.kind == AstKind.AssignmentStatement and #sk.lhs == 1 and #sk.rhs == 1
                            and sk.lhs[1].kind == AstKind.AssignmentIndexing
                            and isVarRef(sk.lhs[1].base, cellSc, cellId)
                            and sk.lhs[1].index.kind == AstKind.NumberExpression
                            and sk.lhs[1].index.value == 1 then
                            isTopSlotWrite = true
                            local rhsIsNil = sk.rhs[1].kind == AstKind.NilExpression
                                or (sk.rhs[1].kind == AstKind.VariableExpression and curNil[varKey(sk.rhs[1].scope, sk.rhs[1].id)] == true)
                            if rhsIsNil then
                                if slotValWriteIdx or totalSlotReads > 0 then
                                    invalidCell = true
                                else
                                    slotNilWriteIdxs[k] = true
                                end
                            else
                                if slotValWriteIdx then
                                    invalidCell = true
                                else
                                    slotValWriteIdx = k
                                end
                            end
                            visitNode(sk.rhs[1], function(n)
                                if isVarRef(n, cellSc, cellId) then invalidCell = true end
                            end, nil, ast.globalScope)
                        end

                        if sk.kind == AstKind.AssignmentStatement and #sk.lhs == 1 and #sk.rhs == 1
                            and sk.lhs[1].kind == AstKind.AssignmentVariable and not sk.lhs[1].scope.isGlobal then
                            local lk = varKey(sk.lhs[1].scope, sk.lhs[1].id)
                            if sk.rhs[1].kind == AstKind.NilExpression
                                or (sk.rhs[1].kind == AstKind.VariableExpression and curNil[varKey(sk.rhs[1].scope, sk.rhs[1].id)]) then
                                curNil[lk] = true
                            else
                                curNil[lk] = nil
                            end
                        else
                            visitNode(sk, function(n)
                                if n.kind == AstKind.AssignmentVariable then
                                    curNil[varKey(n.scope, n.id)] = nil
                                end
                            end, nil, ast.globalScope)
                        end

                        if not isTopSlotWrite and not invalidCell then
                            local allowedRefs = {}
                            visitNode(sk, function(n)
                                if n.kind == AstKind.AssignmentIndexing and isVarRef(n.base, cellSc, cellId) then
                                    invalidCell = true
                                elseif n.kind == AstKind.IndexExpression and isVarRef(n.base, cellSc, cellId) then
                                    if n.index.kind == AstKind.NumberExpression and n.index.value == 1 then
                                        allowedRefs[n.base] = true
                                        totalSlotReads = totalSlotReads + 1
                                    else
                                        invalidCell = true
                                    end
                                elseif n.kind == AstKind.LocalVariableDeclaration and #n.ids == 1 and #n.expressions == 1
                                    and isVarRef(n.expressions[1], cellSc, cellId) then
                                    local skey = varKey(n.scope, n.ids[1])
                                    if (allWrites[skey] or 0) == 1 then
                                        allowedRefs[n.expressions[1]] = true
                                        snapDecls[#snapDecls + 1] = n
                                        snapSet[skey] = { scope = n.scope, id = n.ids[1] }
                                    else
                                        invalidCell = true
                                    end
                                end
                            end, nil, ast.globalScope)

                            if not invalidCell then
                                visitNode(sk, function(n)
                                    if n.kind == AstKind.VariableExpression and n.scope == cellSc and n.id == cellId then
                                        if not allowedRefs[n] then
                                            invalidCell = true
                                        end
                                    end
                                end, nil, ast.globalScope)
                            end
                        end
                        if invalidCell then break end
                    end
                end

                if not invalidCell and next(snapSet) ~= nil then
                    local allowedSnapRefs = {}
                    visitNode(blockNode, function(n)
                        if n.kind == AstKind.AssignmentIndexing and n.base.kind == AstKind.VariableExpression then
                            if snapSet[varKey(n.base.scope, n.base.id)] then
                                invalidCell = true
                            end
                        elseif n.kind == AstKind.IndexExpression and n.base.kind == AstKind.VariableExpression then
                            if snapSet[varKey(n.base.scope, n.base.id)] then
                                if n.index.kind == AstKind.NumberExpression and n.index.value == 1 then
                                    allowedSnapRefs[n.base] = true
                                    totalSlotReads = totalSlotReads + 1
                                else
                                    invalidCell = true
                                end
                            end
                        end
                    end, nil, ast.globalScope)

                    if not invalidCell then
                        visitNode(blockNode, function(n)
                            if n.kind == AstKind.VariableExpression and snapSet[varKey(n.scope, n.id)] then
                                if not allowedSnapRefs[n] then
                                    invalidCell = true
                                end
                            end
                        end, nil, ast.globalScope)
                    end
                end

                if not invalidCell and slotValWriteIdx and totalSlotReads > 0 then
                    local freshId = blockNode.scope:addVariable()
                    newLocalIds[#newLocalIds + 1] = freshId

                    if isLocalDecl then
                        stmts[idx] = Ast.LocalVariableDeclaration(cellSc, { cellId }, {})
                    else
                        stmts[idx] = Ast.AssignmentStatement(
                            { Ast.AssignmentVariable(cellSc, cellId) },
                            { Ast.NilExpression() }
                        )
                    end

                    local valRhs = stmts[slotValWriteIdx].rhs[1]
                    stmts[slotValWriteIdx] = Ast.AssignmentStatement(
                        { Ast.AssignmentVariable(blockNode.scope, freshId) },
                        { valRhs }
                    )

                    local snapDeclLookup = {}
                    for _, sd in ipairs(snapDecls) do snapDeclLookup[sd] = true end

                    for k = idx + 1, rangeEnd do
                        if not slotNilWriteIdxs[k] and k ~= slotValWriteIdx then
                            stmts[k] = visitNode(stmts[k], nil, function(n)
                                if n.kind == AstKind.IndexExpression
                                    and isVarRef(n.base, cellSc, cellId)
                                    and n.index.kind == AstKind.NumberExpression
                                    and n.index.value == 1 then
                                    return Ast.VariableExpression(blockNode.scope, freshId)
                                end
                            end, ast.globalScope)
                        end
                    end

                    for k = rangeEnd, idx + 1, -1 do
                        if slotNilWriteIdxs[k] then
                            table.remove(stmts, k)
                        end
                    end

                    if next(snapSet) ~= nil then
                        local subBlocks = {}
                        visitNode(blockNode, function(subB)
                            if subB.kind == AstKind.Block then
                                subBlocks[#subBlocks + 1] = subB
                            end
                        end, function(n)
                            if n.kind == AstKind.IndexExpression and n.base.kind == AstKind.VariableExpression
                                and snapSet[varKey(n.base.scope, n.base.id)]
                                and n.index.kind == AstKind.NumberExpression
                                and n.index.value == 1 then
                                return Ast.VariableExpression(blockNode.scope, freshId)
                            end
                        end, ast.globalScope)
                        for _, subB in ipairs(subBlocks) do
                            local j = 1
                            while j <= #subB.statements do
                                if snapDeclLookup[subB.statements[j]] then
                                    table.remove(subB.statements, j)
                                else
                                    j = j + 1
                                end
                            end
                        end
                    end

                    anyChanged = true
                    unboxed = true
                end
            end

            if not unboxed then
                idx = idx + 1
            end
        end

        if #newLocalIds > 0 then
            table.insert(blockNode.statements, 1, Ast.LocalVariableDeclaration(blockNode.scope, newLocalIds, {}))
        end
    end

    local _, writesAfterUnbox = countVarUsage(ast)
    local writtenInClosure = {}
    visitast(ast, function(n)
        if n.kind == AstKind.ForStatement then
            local k = varKey(n.scope, n.id)
            writesAfterUnbox[k] = (writesAfterUnbox[k] or 0) + 2
        elseif n.kind == AstKind.ForInStatement then
            for _, id in ipairs(n.ids) do
                local k = varKey(n.scope, id)
                writesAfterUnbox[k] = (writesAfterUnbox[k] or 0) + 2
            end
        elseif n.lhs and n.rhs and n.kind ~= AstKind.AssignmentStatement then
            if n.lhs.kind == AstKind.AssignmentVariable then
                local k = varKey(n.lhs.scope, n.lhs.id)
                writesAfterUnbox[k] = (writesAfterUnbox[k] or 0) + 2
            end
        end
        if FUNCTION_KINDS[n.kind] and n.body then
            local innerOwnScopes = {}
            if n.body.scope and not n.body.scope.isGlobal then
                innerOwnScopes[n.body.scope] = true
            end
            for _, arg in ipairs(n.args or {}) do
                if arg.scope and not arg.scope.isGlobal then
                    innerOwnScopes[arg.scope] = true
                end
            end
            visitNode(n.body, function(m)
                if (m.kind == AstKind.Block or m.kind == AstKind.ForStatement or m.kind == AstKind.ForInStatement or FUNCTION_KINDS[m.kind])
                    and m.scope and not m.scope.isGlobal then
                    innerOwnScopes[m.scope] = true
                end
            end, nil, ast.globalScope)
            visitNode(n.body, function(m)
                if m.kind == AstKind.AssignmentVariable and not m.scope.isGlobal and not innerOwnScopes[m.scope] then
                    writtenInClosure[varKey(m.scope, m.id)] = true
                elseif m.lhs and m.rhs and m.kind ~= AstKind.AssignmentStatement
                    and m.lhs.kind == AstKind.AssignmentVariable
                    and not m.lhs.scope.isGlobal and not innerOwnScopes[m.lhs.scope] then
                    writtenInClosure[varKey(m.lhs.scope, m.lhs.id)] = true
                end
            end, nil, ast.globalScope)
        end
    end)

    local function isPropagatableExpr(expr)
        if not expr then return false end
        if expr.kind == AstKind.StringExpression
            or expr.kind == AstKind.NumberExpression
            or expr.kind == AstKind.BooleanExpression then
            return true
        end
        if expr.kind == AstKind.VariableExpression and not expr.scope.isGlobal then
            local tk = varKey(expr.scope, expr.id)
            if (writesAfterUnbox[tk] or 0) == 1 and not writtenInClosure[tk] then
                return true
            end
        end
        return false
    end

    visitast(ast, function(blk)
        if blk.kind ~= AstKind.Block then return end
        local bstmts = blk.statements
        local known = {}

        local function subKnownInExpr(exprNode)
            if next(known) == nil then return exprNode end
            return visitNode(exprNode, function(n)
                if FUNCTION_KINDS[n.kind] then return nil, true end
            end, function(n)
                if n.kind == AstKind.VariableExpression and not n.scope.isGlobal then
                    local kv = known[varKey(n.scope, n.id)]
                    if kv then
                        anyChanged = true
                        return cloneSimpleExpr(kv)
                    end
                end
            end, ast.globalScope)
        end

        for i = 1, #bstmts do
            local s = bstmts[i]
            if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                and s.lhs[1].kind == AstKind.AssignmentVariable and not s.lhs[1].scope.isGlobal then
                s.rhs[1] = subKnownInExpr(s.rhs[1])
                local lk = varKey(s.lhs[1].scope, s.lhs[1].id)
                if not writtenInClosure[lk] and isPropagatableExpr(s.rhs[1])
                    and not isVarRef(s.rhs[1], s.lhs[1].scope, s.lhs[1].id) then
                    known[lk] = s.rhs[1]
                else
                    known[lk] = nil
                end
            elseif s.kind == AstKind.LocalVariableDeclaration then
                if s.expressions then
                    for eIdx = 1, #s.expressions do
                        s.expressions[eIdx] = subKnownInExpr(s.expressions[eIdx])
                    end
                end
                for idIdx = 1, #s.ids do
                    local lk = varKey(s.scope, s.ids[idIdx])
                    local ex = s.expressions and s.expressions[idIdx]
                    if ex and (#s.ids == #s.expressions) and not writtenInClosure[lk] and isPropagatableExpr(ex) then
                        known[lk] = ex
                    else
                        known[lk] = nil
                    end
                end
            elseif s.kind == AstKind.ReturnStatement then
                for aIdx = 1, #s.args do
                    s.args[aIdx] = subKnownInExpr(s.args[aIdx])
                end
            elseif s.kind == AstKind.FunctionCallStatement or s.kind == AstKind.PassSelfFunctionCallStatement then
                s.base = subKnownInExpr(s.base)
                for aIdx = 1, #s.args do
                    s.args[aIdx] = subKnownInExpr(s.args[aIdx])
                end
            elseif s.kind == AstKind.AssignmentStatement then
                for lIdx = 1, #s.lhs do
                    if s.lhs[lIdx].kind == AstKind.AssignmentIndexing then
                        s.lhs[lIdx].base = subKnownInExpr(s.lhs[lIdx].base)
                        s.lhs[lIdx].index = subKnownInExpr(s.lhs[lIdx].index)
                    end
                end
                for rIdx = 1, #s.rhs do
                    s.rhs[rIdx] = subKnownInExpr(s.rhs[rIdx])
                end
                for lIdx = 1, #s.lhs do
                    if s.lhs[lIdx].kind == AstKind.AssignmentVariable then
                        known[varKey(s.lhs[lIdx].scope, s.lhs[lIdx].id)] = nil
                    end
                end
            else
                if s.kind == AstKind.IfStatement then
                    s.condition = subKnownInExpr(s.condition)
                end
                visitNode(s, function(n)
                    if n.kind == AstKind.AssignmentVariable then
                        known[varKey(n.scope, n.id)] = nil
                    elseif n.kind == AstKind.LocalVariableDeclaration then
                        for _, id in ipairs(n.ids) do
                            known[varKey(n.scope, id)] = nil
                        end
                    end
                end, nil, ast.globalScope)
            end
        end
    end)

    local hasWeakMode = false
    visitast(ast, function(n)
        if n.kind == AstKind.StringExpression and n.value == "__mode" then
            hasWeakMode = true
        end
    end)
    if hasWeakMode then
        visitast(ast, function(blk)
            if blk.kind ~= AstKind.Block then return end
            local bstmts = blk.statements
            local i = 1
            while i + 2 <= #bstmts do
                local s1, s2, s3 = bstmts[i], bstmts[i + 1], bstmts[i + 2]
                if s1.kind == AstKind.AssignmentStatement and #s1.lhs == 1 and #s1.rhs == 1
                    and s1.lhs[1].kind == AstKind.AssignmentVariable and not s1.lhs[1].scope.isGlobal
                    and s1.rhs[1].kind == AstKind.TableConstructorExpression and #s1.rhs[1].entries == 0
                    and s2.kind == AstKind.AssignmentStatement and #s2.lhs == 1 and #s2.rhs == 1
                    and s2.lhs[1].kind == AstKind.AssignmentIndexing
                    and isVarRef(s2.rhs[1], s1.lhs[1].scope, s1.lhs[1].id)
                    and not isVarRef(s2.lhs[1].base, s1.lhs[1].scope, s1.lhs[1].id)
                    and not isVarRef(s2.lhs[1].index, s1.lhs[1].scope, s1.lhs[1].id)
                    and s3.kind == AstKind.AssignmentStatement and #s3.lhs == 1 and #s3.rhs == 1
                    and s3.lhs[1].kind == AstKind.AssignmentVariable
                    and s3.lhs[1].scope == s1.lhs[1].scope and s3.lhs[1].id == s1.lhs[1].id
                    and s3.rhs[1].kind == AstKind.NilExpression then
                    local doSc = Scope:new(blk.scope)
                    local tmpId = doSc:addVariable()
                    local doStmts = {
                        Ast.LocalVariableDeclaration(doSc, { tmpId }, { Ast.TableConstructorExpression({}) }),
                        Ast.AssignmentStatement(
                            { s2.lhs[1] },
                            { Ast.VariableExpression(doSc, tmpId) }
                        ),
                        Ast.AssignmentStatement(
                            { Ast.AssignmentVariable(doSc, tmpId) },
                            { Ast.NilExpression() }
                        ),
                    }
                    bstmts[i] = Ast.DoStatement(Ast.Block(doStmts, doSc))
                    bstmts[i + 1] = Ast.AssignmentStatement(
                        { Ast.AssignmentVariable(s1.lhs[1].scope, s1.lhs[1].id) },
                        { Ast.NilExpression() }
                    )
                    table.remove(bstmts, i + 2)
                    anyChanged = true
                    i = i + 2
                else
                    i = i + 1
                end
            end
        end)
    end

    return anyChanged
end

local function reparentDirectChildBlocks(blockNode, oldParentScope, newParentScope)
    visitNode(blockNode, function(n)
        if n == blockNode then return end
        if n.kind == AstKind.Block and n.scope then
            if n.scope.parentScope == oldParentScope and n.scope ~= newParentScope then
                n.scope:setParent(newParentScope)
            end
            return nil, true
        end
        if (n.kind == AstKind.ForStatement or n.kind == AstKind.ForInStatement
            or FUNCTION_KINDS[n.kind]) and n.scope then
            if n.scope.parentScope == oldParentScope and n.scope ~= newParentScope then
                n.scope:setParent(newParentScope)
            end
            return nil, true
        end
    end, nil, nil)
end

local function collectClosureCaptures(ast)
    local capturedRead = {}
    local capturedWrite = {}
    visitast(ast, function(n)
        if FUNCTION_KINDS[n.kind] and n.body then
            local ownScopes = {}
            if n.body.scope and not n.body.scope.isGlobal then
                ownScopes[n.body.scope] = true
            end
            for _, arg in ipairs(n.args or {}) do
                if arg.scope and not arg.scope.isGlobal then
                    ownScopes[arg.scope] = true
                end
            end
            visitNode(n.body, function(m)
                if (m.kind == AstKind.Block or m.kind == AstKind.ForStatement or m.kind == AstKind.ForInStatement or FUNCTION_KINDS[m.kind])
                    and m.scope and not m.scope.isGlobal then
                    ownScopes[m.scope] = true
                end
            end, nil, ast.globalScope)
            visitNode(n.body, function(m)
                if m.kind == AstKind.VariableExpression and not m.scope.isGlobal and not ownScopes[m.scope] then
                    capturedRead[varKey(m.scope, m.id)] = true
                elseif m.kind == AstKind.AssignmentVariable and not m.scope.isGlobal and not ownScopes[m.scope] then
                    local k = varKey(m.scope, m.id)
                    capturedRead[k] = true
                    capturedWrite[k] = true
                elseif m.lhs and m.rhs and m.kind ~= AstKind.AssignmentStatement
                    and m.lhs.kind == AstKind.AssignmentVariable
                    and not m.lhs.scope.isGlobal and not ownScopes[m.lhs.scope] then
                    local k = varKey(m.lhs.scope, m.lhs.id)
                    capturedRead[k] = true
                    capturedWrite[k] = true
                end
            end, nil, ast.globalScope)
        end
    end)
    return capturedRead, capturedWrite
end

local function isNilAssignStmt(s)
    return s and s.kind == AstKind.AssignmentStatement
        and #s.lhs == 1 and #s.rhs == 1
        and s.lhs[1].kind == AstKind.AssignmentVariable
        and not s.lhs[1].scope.isGlobal
        and s.rhs[1].kind == AstKind.NilExpression
end

local function isSameVar(node, scope, id)
    return node and (node.kind == AstKind.VariableExpression or node.kind == AstKind.AssignmentVariable)
        and node.scope == scope and node.id == id
end

local function isMultiReturnExpr(e)
    if not e then return false end
    return e.kind == AstKind.FunctionCallExpression
        or e.kind == AstKind.PassSelfFunctionCallExpression
        or e.kind == AstKind.VarargExpression
end

local function isPureConstOrFnExpr(e, disallowedScopes)
    if not e then return false end
    local k = e.kind
    if k == AstKind.NumberExpression
        or k == AstKind.StringExpression
        or k == AstKind.BooleanExpression
        or k == AstKind.NilExpression then
        return true
    end
    if k == AstKind.FunctionLiteralExpression then
        if disallowedScopes then
            local bad = false
            visitNode(e, function(n)
                if (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable)
                    and n.scope and disallowedScopes[n.scope] then
                    bad = true
                end
            end, nil, nil)
            if bad then return false end
        end
        return true
    end
    return false
end

local function stmtHasObservableEffect(s, globalScope)
    if not s then return true end
    local impure = false
    if s.kind == AstKind.AssignmentStatement then
        for i = 1, #s.lhs do
            if s.lhs[i].kind == AstKind.AssignmentIndexing or s.lhs[i].scope.isGlobal then
                return true
            end
        end
        for i = 1, #s.rhs do
            visitNode(s.rhs[i], function(n)
                if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                if n.kind == AstKind.FunctionCallExpression
                    or n.kind == AstKind.PassSelfFunctionCallExpression
                    or n.kind == AstKind.IndexExpression then
                    impure = true
                end
            end, nil, globalScope)
        end
        return impure
    elseif s.kind == AstKind.LocalVariableDeclaration then
        if s.expressions then
            for i = 1, #s.expressions do
                visitNode(s.expressions[i], function(n)
                    if n.kind == AstKind.FunctionLiteralExpression then return nil, true end
                    if n.kind == AstKind.FunctionCallExpression
                        or n.kind == AstKind.PassSelfFunctionCallExpression
                        or n.kind == AstKind.IndexExpression then
                        impure = true
                    end
                end, nil, globalScope)
            end
        end
        return impure
    elseif s.kind == AstKind.LocalFunctionDeclaration then
        return false
    end
    return true
end

local function reconstructCffLoopsInBlock(blockNode, capturedRead, tonumberVars, errorVars, globalScope)
    local stmts = blockNode.statements
    local changed = false

    local function matchForCoerceExpr(stmt, expectedSubstr)
        if not stmt or stmt.kind ~= AstKind.AssignmentStatement or #stmt.lhs ~= 1 or #stmt.rhs ~= 1 then
            return nil, nil
        end
        if stmt.lhs[1].kind ~= AstKind.AssignmentVariable or stmt.lhs[1].scope.isGlobal then
            return nil, nil
        end
        local rhs = stmt.rhs[1]
        if rhs.kind ~= AstKind.OrExpression then return nil, nil end
        local c1, c2 = rhs.lhs, rhs.rhs
        if c1.kind ~= AstKind.FunctionCallExpression or #c1.args ~= 1 then return nil, nil end
        if c2.kind ~= AstKind.FunctionCallExpression or #c2.args ~= 1 then return nil, nil end
        if c2.args[1].kind ~= AstKind.StringExpression or not string.find(c2.args[1].value, expectedSubstr, 1, true) then
            return nil, nil
        end
        local isTn = isGlobalVar(c1.base, "tonumber")
            or (c1.base.kind == AstKind.VariableExpression and tonumberVars[varKey(c1.base.scope, c1.base.id)])
        local isErr = isGlobalVar(c2.base, "error")
            or (c2.base.kind == AstKind.VariableExpression and errorVars[varKey(c2.base.scope, c2.base.id)])
        if not isTn or not isErr then return nil, nil end
        return stmt.lhs[1], c1.args[1]
    end

    local function varReferencedAfter(sc, id, startIdx)
        local key = varKey(sc, id)
        for j = startIdx, #stmts do
            local sj = stmts[j]
            if sj.kind == AstKind.AssignmentStatement and #sj.lhs == 1
                and sj.lhs[1].kind == AstKind.AssignmentVariable
                and varKey(sj.lhs[1].scope, sj.lhs[1].id) == key then
                local r = false
                visitNode(sj.rhs[1], function(n)
                    if isVarRef(n, sc, id) then r = true end
                end, nil, globalScope)
                return r
            end
            local r = false
            visitNode(sj, function(n)
                if isVarRef(n, sc, id) then r = true end
            end, nil, globalScope)
            if r then return true end
        end
        return false
    end

    local i = 1
    while i <= #stmts do
        local matched = false
        local initV, startExpr = matchForCoerceExpr(stmts[i], "initial value must be a number")
        if initV and i + 5 <= #stmts then
            local limitV, limitExpr = matchForCoerceExpr(stmts[i + 1], "limit must be a number")
            local stepV, stepExpr = matchForCoerceExpr(stmts[i + 2], "step must be a number")
            local negSt = stmts[i + 3]
            local subSt = stmts[i + 4]
            if limitV and stepV and negSt and subSt
                and negSt.kind == AstKind.AssignmentStatement and #negSt.lhs == 1 and #negSt.rhs == 1
                and negSt.lhs[1].kind == AstKind.AssignmentVariable and not negSt.lhs[1].scope.isGlobal
                and subSt.kind == AstKind.AssignmentStatement and #subSt.lhs == 1 and #subSt.rhs == 1
                and subSt.lhs[1].kind == AstKind.AssignmentVariable and not subSt.lhs[1].scope.isGlobal
                and subSt.rhs[1].kind == AstKind.SubExpression
                and isVarRef(subSt.rhs[1].lhs, initV.scope, initV.id)
                and isVarRef(subSt.rhs[1].rhs, stepV.scope, stepV.id) then
                local negV = negSt.lhs[1]
                local idxV = subSt.lhs[1]
                local negOk = (negSt.rhs[1].kind == AstKind.GreaterThanExpression
                        and negSt.rhs[1].lhs.kind == AstKind.NumberExpression and negSt.rhs[1].lhs.value == 0
                        and isVarRef(negSt.rhs[1].rhs, stepV.scope, stepV.id))
                    or (negSt.rhs[1].kind == AstKind.LessThanExpression
                        and isVarRef(negSt.rhs[1].lhs, stepV.scope, stepV.id)
                        and negSt.rhs[1].rhs.kind == AstKind.NumberExpression and negSt.rhs[1].rhs.value == 0)
                local wPos = i + 5
                if wPos <= #stmts and isNilAssignStmt(stmts[wPos])
                    and isSameVar(stmts[wPos].lhs[1], initV.scope, initV.id) then
                    wPos = wPos + 1
                end
                local ws = stmts[wPos]
                if negOk and ws and ws.kind == AstKind.WhileStatement
                    and ws.condition.kind == AstKind.BooleanExpression and ws.condition.value == true
                    and not capturedRead[varKey(initV.scope, initV.id)]
                    and not capturedRead[varKey(limitV.scope, limitV.id)]
                    and not capturedRead[varKey(stepV.scope, stepV.id)]
                    and not capturedRead[varKey(negV.scope, negV.id)]
                    and not capturedRead[varKey(idxV.scope, idxV.id)] then
                    local wb = ws.body.statements
                    local p = 1
                    local stepIncOk = false
                    if p <= #wb and wb[p].kind == AstKind.AssignmentStatement and #wb[p].lhs == 1 and #wb[p].rhs == 1
                        and isSameVar(wb[p].lhs[1], idxV.scope, idxV.id)
                        and wb[p].rhs[1].kind == AstKind.AddExpression then
                        local al, ar = wb[p].rhs[1].lhs, wb[p].rhs[1].rhs
                        if (isVarRef(al, idxV.scope, idxV.id) and isVarRef(ar, stepV.scope, stepV.id))
                            or (isVarRef(al, stepV.scope, stepV.id) and isVarRef(ar, idxV.scope, idxV.id)) then
                            stepIncOk = true
                            p = p + 1
                        end
                    end
                    while p <= #wb and isNilAssignStmt(wb[p]) do p = p + 1 end
                    local bodyRest = nil
                    if stepIncOk and p <= #wb and wb[p].kind == AstKind.IfStatement and #wb[p].elseifs == 0 then
                        local ifs = wb[p]
                        local bStmts = ifs.body.statements
                        local eStmts = ifs.elsebody and ifs.elsebody.statements or {}
                        if ifs.condition.kind == AstKind.NotExpression and #eStmts == 0
                            and #bStmts >= 1 and bStmts[#bStmts].kind == AstKind.BreakStatement then
                            local allNils = true
                            for q = 1, #bStmts - 1 do
                                if not isNilAssignStmt(bStmts[q]) then allNils = false end
                            end
                            if allNils then
                                bodyRest = {}
                                for q = p + 1, #wb do bodyRest[#bodyRest + 1] = wb[q] end
                            end
                        elseif #eStmts >= 1 and eStmts[#eStmts].kind == AstKind.BreakStatement and p == #wb then
                            local allNils = true
                            for q = 1, #eStmts - 1 do
                                if not isNilAssignStmt(eStmts[q]) then allNils = false end
                            end
                            if allNils then
                                bodyRest = {}
                                for q = 1, #bStmts do bodyRest[#bodyRest + 1] = bStmts[q] end
                            end
                        end
                    end

                    if bodyRest and not varReferencedAfter(limitV.scope, limitV.id, wPos + 1)
                        and not varReferencedAfter(stepV.scope, stepV.id, wPos + 1)
                        and not varReferencedAfter(negV.scope, negV.id, wPos + 1)
                        and not varReferencedAfter(idxV.scope, idxV.id, wPos + 1) then
                        local internalKeys = {
                            [varKey(limitV.scope, limitV.id)] = true,
                            [varKey(stepV.scope, stepV.id)] = true,
                            [varKey(negV.scope, negV.id)] = true,
                        }
                        local internalTouched = false
                        local idxWritten = false
                        for _, bs in ipairs(bodyRest) do
                            visitNode(bs, function(n)
                                if (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable)
                                    and not n.scope.isGlobal and internalKeys[varKey(n.scope, n.id)] then
                                    internalTouched = true
                                end
                                if n.kind == AstKind.AssignmentVariable and isSameVar(n, idxV.scope, idxV.id) then
                                    idxWritten = true
                                end
                            end, nil, globalScope)
                        end
                        if not internalTouched and not idxWritten then
                            local userV = nil
                            if #bodyRest >= 1 and bodyRest[1].kind == AstKind.AssignmentStatement
                                and #bodyRest[1].lhs == 1 and #bodyRest[1].rhs == 1
                                and bodyRest[1].lhs[1].kind == AstKind.AssignmentVariable
                                and not bodyRest[1].lhs[1].scope.isGlobal
                                and isVarRef(bodyRest[1].rhs[1], idxV.scope, idxV.id) then
                                local cand = bodyRest[1].lhs[1]
                                if not capturedRead[varKey(cand.scope, cand.id)]
                                    and not varReferencedAfter(cand.scope, cand.id, wPos + 1) then
                                    local idxStillRead = false
                                    for q = 2, #bodyRest do
                                        visitNode(bodyRest[q], function(n)
                                            if isVarRef(n, idxV.scope, idxV.id) then idxStillRead = true end
                                        end, nil, globalScope)
                                    end
                                    if not idxStillRead then
                                        userV = cand
                                        table.remove(bodyRest, 1)
                                    end
                                end
                            end

                            if userV and #bodyRest >= 1 and isNilAssignStmt(bodyRest[#bodyRest])
                                and isSameVar(bodyRest[#bodyRest].lhs[1], userV.scope, userV.id) then
                                table.remove(bodyRest, #bodyRest)
                            end

                            local forScope = Scope:new(blockNode.scope)
                            local loopId = forScope:addVariable()
                            local targetKey = userV and varKey(userV.scope, userV.id) or varKey(idxV.scope, idxV.id)
                            local forBody = Ast.Block(bodyRest, forScope)
                            reparentDirectChildBlocks(forBody, ws.body.scope, forScope)
                            visitNode(forBody, nil, function(n)
                                if n.kind == AstKind.VariableExpression and not n.scope.isGlobal
                                    and varKey(n.scope, n.id) == targetKey then
                                    return Ast.VariableExpression(forScope, loopId)
                                elseif n.kind == AstKind.AssignmentVariable and not n.scope.isGlobal
                                    and varKey(n.scope, n.id) == targetKey then
                                    return Ast.AssignmentVariable(forScope, loopId)
                                end
                            end, globalScope)

                            local afterEnd = wPos + 1
                            while afterEnd <= #stmts and isNilAssignStmt(stmts[afterEnd]) do
                                local nk = varKey(stmts[afterEnd].lhs[1].scope, stmts[afterEnd].lhs[1].id)
                                if nk == varKey(limitV.scope, limitV.id)
                                    or nk == varKey(stepV.scope, stepV.id)
                                    or nk == varKey(negV.scope, negV.id)
                                    or nk == varKey(idxV.scope, idxV.id)
                                    or nk == varKey(initV.scope, initV.id)
                                    or (userV and nk == varKey(userV.scope, userV.id)) then
                                    afterEnd = afterEnd + 1
                                else
                                    break
                                end
                            end

                            local forStmt = Ast.ForStatement(forScope, loopId, startExpr, limitExpr, stepExpr, forBody, blockNode.scope)
                            stmts[i] = forStmt
                            for rem = afterEnd - 1, i + 1, -1 do
                                table.remove(stmts, rem)
                            end
                            changed = true
                            matched = true
                        end
                    end
                end
            end
        end

        if not matched and i + 4 <= #stmts then
            local s0 = stmts[i]
            if s0.kind == AstKind.AssignmentStatement and #s0.lhs == 1 and #s0.rhs == 1
                and s0.lhs[1].kind == AstKind.AssignmentVariable and not s0.lhs[1].scope.isGlobal
                and s0.rhs[1].kind == AstKind.TableConstructorExpression
                and #s0.rhs[1].entries >= 1 then
                local allPlainEntries = true
                local iterExprs = {}
                for _, ent in ipairs(s0.rhs[1].entries) do
                    if ent.kind ~= AstKind.TableEntry then allPlainEntries = false break end
                    iterExprs[#iterExprs + 1] = ent.value
                end
                local tV = s0.lhs[1]
                local slots = {}
                local okSlots = allPlainEntries
                for off = 1, 3 do
                    local sk = stmts[i + off]
                    if not sk or sk.kind ~= AstKind.AssignmentStatement or #sk.lhs ~= 1 or #sk.rhs ~= 1
                        or sk.lhs[1].kind ~= AstKind.AssignmentVariable or sk.lhs[1].scope.isGlobal
                        or sk.rhs[1].kind ~= AstKind.IndexExpression
                        or not isVarRef(sk.rhs[1].base, tV.scope, tV.id)
                        or sk.rhs[1].index.kind ~= AstKind.NumberExpression then
                        okSlots = false
                        break
                    end
                    local idxNum = sk.rhs[1].index.value
                    if (idxNum ~= 1 and idxNum ~= 2 and idxNum ~= 3) or slots[idxNum] then
                        okSlots = false
                        break
                    end
                    slots[idxNum] = sk.lhs[1]
                end
                if okSlots then
                    local fV, sV, varV = slots[1], slots[2], slots[3]
                    local wPos = i + 4
                    if wPos <= #stmts and isNilAssignStmt(stmts[wPos])
                        and isSameVar(stmts[wPos].lhs[1], tV.scope, tV.id) then
                        wPos = wPos + 1
                    end
                    local ws = stmts[wPos]
                    if ws and ws.kind == AstKind.WhileStatement
                        and ws.condition.kind == AstKind.BooleanExpression and ws.condition.value == true
                        and not capturedRead[varKey(tV.scope, tV.id)]
                        and not capturedRead[varKey(fV.scope, fV.id)]
                        and not capturedRead[varKey(sV.scope, sV.id)]
                        and not capturedRead[varKey(varV.scope, varV.id)] then
                        local wb = ws.body.statements
                        if #wb >= 2 and wb[1].kind == AstKind.AssignmentStatement
                            and #wb[1].lhs >= 1 and #wb[1].rhs == 1
                            and wb[1].rhs[1].kind == AstKind.FunctionCallExpression
                            and isVarRef(wb[1].rhs[1].base, fV.scope, fV.id)
                            and #wb[1].rhs[1].args == 2
                            and isVarRef(wb[1].rhs[1].args[1], sV.scope, sV.id)
                            and isVarRef(wb[1].rhs[1].args[2], varV.scope, varV.id)
                            and isSameVar(wb[1].lhs[1], varV.scope, varV.id) then
                            local allLhsVars = true
                            for _, lv in ipairs(wb[1].lhs) do
                                if lv.kind ~= AstKind.AssignmentVariable or lv.scope.isGlobal
                                    or capturedRead[varKey(lv.scope, lv.id)] then
                                    allLhsVars = false
                                end
                            end
                            local ifs = wb[2]
                            local guardOk = false
                            if allLhsVars and ifs.kind == AstKind.IfStatement and #ifs.elseifs == 0
                                and (not ifs.elsebody or #ifs.elsebody.statements == 0) then
                                local cond = ifs.condition
                                local isBreakCond = (cond.kind == AstKind.NotExpression and isVarRef(cond.rhs, varV.scope, varV.id))
                                    or (cond.kind == AstKind.EqualsExpression
                                        and ((isVarRef(cond.lhs, varV.scope, varV.id) and cond.rhs.kind == AstKind.NilExpression)
                                            or (isVarRef(cond.rhs, varV.scope, varV.id) and cond.lhs.kind == AstKind.NilExpression)))
                                local ib = ifs.body.statements
                                if isBreakCond and #ib >= 1 and ib[#ib].kind == AstKind.BreakStatement then
                                    guardOk = true
                                    for q = 1, #ib - 1 do
                                        if not isNilAssignStmt(ib[q]) then guardOk = false end
                                    end
                                end
                            end
                            if guardOk and not varReferencedAfter(tV.scope, tV.id, wPos + 1)
                                and not varReferencedAfter(fV.scope, fV.id, wPos + 1)
                                and not varReferencedAfter(sV.scope, sV.id, wPos + 1)
                                and not varReferencedAfter(varV.scope, varV.id, wPos + 1) then
                                local bodyRest = {}
                                for q = 3, #wb do bodyRest[#bodyRest + 1] = wb[q] end
                                local unsafe = false
                                for idxL = 2, #wb[1].lhs do
                                    if varReferencedAfter(wb[1].lhs[idxL].scope, wb[1].lhs[idxL].id, wPos + 1) then
                                        unsafe = true
                                    end
                                end
                                local lhsKeyLookup = {}
                                for _, lv in ipairs(wb[1].lhs) do
                                    lhsKeyLookup[varKey(lv.scope, lv.id)] = true
                                end
                                local fsKeys = {
                                    [varKey(fV.scope, fV.id)] = true,
                                    [varKey(sV.scope, sV.id)] = true,
                                }
                                if not lhsKeyLookup[varKey(tV.scope, tV.id)] then
                                    fsKeys[varKey(tV.scope, tV.id)] = true
                                end
                                for _, bs in ipairs(bodyRest) do
                                    visitNode(bs, function(n)
                                        if (n.kind == AstKind.VariableExpression or n.kind == AstKind.AssignmentVariable)
                                            and not n.scope.isGlobal and fsKeys[varKey(n.scope, n.id)] then
                                            unsafe = true
                                        end
                                        if n.kind == AstKind.AssignmentVariable and isSameVar(n, varV.scope, varV.id) then
                                            unsafe = true
                                        end
                                    end, nil, globalScope)
                                end
                                if not unsafe then
                                    local lhsKeyMap = {}
                                    local forScope = Scope:new(blockNode.scope)
                                    local loopIds = {}
                                    for idxL, lv in ipairs(wb[1].lhs) do
                                        local nid = forScope:addVariable()
                                        loopIds[idxL] = nid
                                        lhsKeyMap[varKey(lv.scope, lv.id)] = nid
                                    end
                                    while #bodyRest >= 1 and isNilAssignStmt(bodyRest[#bodyRest])
                                        and lhsKeyMap[varKey(bodyRest[#bodyRest].lhs[1].scope, bodyRest[#bodyRest].lhs[1].id)] do
                                        table.remove(bodyRest, #bodyRest)
                                    end
                                    local forBody = Ast.Block(bodyRest, forScope)
                                    reparentDirectChildBlocks(forBody, ws.body.scope, forScope)
                                    visitNode(forBody, nil, function(n)
                                        if n.kind == AstKind.VariableExpression and not n.scope.isGlobal then
                                            local nid = lhsKeyMap[varKey(n.scope, n.id)]
                                            if nid then return Ast.VariableExpression(forScope, nid) end
                                        elseif n.kind == AstKind.AssignmentVariable and not n.scope.isGlobal then
                                            local nid = lhsKeyMap[varKey(n.scope, n.id)]
                                            if nid then return Ast.AssignmentVariable(forScope, nid) end
                                        end
                                    end, globalScope)

                                    local afterEnd = wPos + 1
                                    while afterEnd <= #stmts and isNilAssignStmt(stmts[afterEnd]) do
                                        local nk = varKey(stmts[afterEnd].lhs[1].scope, stmts[afterEnd].lhs[1].id)
                                        if fsKeys[nk] or lhsKeyMap[nk] then
                                            afterEnd = afterEnd + 1
                                        else
                                            break
                                        end
                                    end

                                    stmts[i] = Ast.ForInStatement(forScope, loopIds, iterExprs, forBody, blockNode.scope)
                                    for rem = afterEnd - 1, i + 1, -1 do
                                        table.remove(stmts, rem)
                                    end
                                    changed = true
                                    matched = true
                                end
                            end
                        end
                    end
                end
            end
        end

        i = i + 1
    end

    return changed
end

local function tryInlineIntoStmt(targetStmt, vScope, vId, rhs, rhsIsPure, rhsNeedsSingleVal)
    local replaced = false
    local aborted = false
    local passedImpure = false

    local function makeReplacement(inTailMultiSlot)
        if rhsNeedsSingleVal and inTailMultiSlot then
            rhs.isParenthesizedExpression = true
        end
        return rhs
    end

    local function walkExpr(e, inTailMultiSlot)
        if aborted or not e then return e end
        local k = e.kind
        if k == AstKind.VariableExpression then
            if e.scope == vScope and e.id == vId then
                if not replaced and (not passedImpure or rhsIsPure) then
                    replaced = true
                    return makeReplacement(inTailMultiSlot)
                else
                    aborted = true
                    return e
                end
            end
            if e.scope.isGlobal and not rhsIsPure then
                passedImpure = true
            end
            return e
        end
        if k == AstKind.NumberExpression or k == AstKind.StringExpression
            or k == AstKind.BooleanExpression or k == AstKind.NilExpression
            or k == AstKind.VarargExpression or k == AstKind.FunctionLiteralExpression then
            return e
        end
        if k == AstKind.IndexExpression then
            e.base = walkExpr(e.base, false)
            e.index = walkExpr(e.index, false)
            passedImpure = true
            return e
        end
        if k == AstKind.FunctionCallExpression then
            e.base = walkExpr(e.base, false)
            for idx = 1, #e.args do
                e.args[idx] = walkExpr(e.args[idx], idx == #e.args)
            end
            passedImpure = true
            return e
        end
        if k == AstKind.PassSelfFunctionCallExpression then
            e.base = walkExpr(e.base, false)
            passedImpure = true
            for idx = 1, #e.args do
                e.args[idx] = walkExpr(e.args[idx], idx == #e.args)
            end
            return e
        end
        if k == AstKind.NotExpression then
            e.rhs = walkExpr(e.rhs, false)
            return e
        end
        if k == AstKind.NegateExpression or k == AstKind.LenExpression then
            e.rhs = walkExpr(e.rhs, false)
            passedImpure = true
            return e
        end
        if k == AstKind.AndExpression or k == AstKind.OrExpression then
            e.lhs = walkExpr(e.lhs, false)
            if rhsIsPure and not replaced then
                e.rhs = walkExpr(e.rhs, false)
            else
                passedImpure = true
            end
            return e
        end
        if k == AstKind.IfElseExpression then
            e.condition = walkExpr(e.condition, false)
            if rhsIsPure and not replaced then
                e.true_value = walkExpr(e.true_value, false)
                if e.elseifs then
                    for idx = 1, #e.elseifs do
                        e.elseifs[idx].condition = walkExpr(e.elseifs[idx].condition, false)
                        e.elseifs[idx].value = walkExpr(e.elseifs[idx].value, false)
                    end
                end
                e.false_value = walkExpr(e.false_value, false)
            else
                passedImpure = true
            end
            return e
        end
        if k == AstKind.TableConstructorExpression then
            for idx = 1, #e.entries do
                local ent = e.entries[idx]
                if ent.kind == AstKind.KeyedTableEntry then
                    ent.key = walkExpr(ent.key, false)
                    ent.value = walkExpr(ent.value, false)
                else
                    ent.value = walkExpr(ent.value, idx == #e.entries)
                end
            end
            return e
        end
        if e.lhs and e.rhs then
            e.lhs = walkExpr(e.lhs, false)
            e.rhs = walkExpr(e.rhs, false)
            if k ~= AstKind.EqualsExpression and k ~= AstKind.NotEqualsExpression then
                passedImpure = true
            else
                passedImpure = true
            end
            return e
        end
        passedImpure = true
        return e
    end

    local sk = targetStmt.kind
    if sk == AstKind.LocalVariableDeclaration then
        if targetStmt.expressions then
            local needTailParen = #targetStmt.ids > #targetStmt.expressions
            for idx = 1, #targetStmt.expressions do
                targetStmt.expressions[idx] = walkExpr(targetStmt.expressions[idx], needTailParen and idx == #targetStmt.expressions)
            end
        end
    elseif sk == AstKind.AssignmentStatement then
        for idx = 1, #targetStmt.lhs do
            if targetStmt.lhs[idx].kind == AstKind.AssignmentIndexing then
                targetStmt.lhs[idx].base = walkExpr(targetStmt.lhs[idx].base, false)
                targetStmt.lhs[idx].index = walkExpr(targetStmt.lhs[idx].index, false)
            end
        end
        local needTailParen = #targetStmt.lhs > #targetStmt.rhs
        for idx = 1, #targetStmt.rhs do
            targetStmt.rhs[idx] = walkExpr(targetStmt.rhs[idx], needTailParen and idx == #targetStmt.rhs)
        end
    elseif sk == AstKind.FunctionCallStatement then
        targetStmt.base = walkExpr(targetStmt.base, false)
        for idx = 1, #targetStmt.args do
            targetStmt.args[idx] = walkExpr(targetStmt.args[idx], idx == #targetStmt.args)
        end
    elseif sk == AstKind.PassSelfFunctionCallStatement then
        targetStmt.base = walkExpr(targetStmt.base, false)
        passedImpure = true
        for idx = 1, #targetStmt.args do
            targetStmt.args[idx] = walkExpr(targetStmt.args[idx], idx == #targetStmt.args)
        end
    elseif sk == AstKind.ReturnStatement then
        for idx = 1, #targetStmt.args do
            targetStmt.args[idx] = walkExpr(targetStmt.args[idx], idx == #targetStmt.args)
        end
    elseif sk == AstKind.IfStatement then
        targetStmt.condition = walkExpr(targetStmt.condition, false)
    elseif sk == AstKind.ForStatement then
        targetStmt.initialValue = walkExpr(targetStmt.initialValue, false)
        targetStmt.finalValue = walkExpr(targetStmt.finalValue, false)
        if targetStmt.incrementBy then
            targetStmt.incrementBy = walkExpr(targetStmt.incrementBy, false)
        end
    elseif sk == AstKind.ForInStatement then
        local needTailParen = #targetStmt.expressions < 3
        for idx = 1, #targetStmt.expressions do
            targetStmt.expressions[idx] = walkExpr(targetStmt.expressions[idx], needTailParen and idx == #targetStmt.expressions)
        end
    elseif targetStmt.lhs and targetStmt.rhs then
        if targetStmt.lhs.kind == AstKind.AssignmentIndexing then
            targetStmt.lhs.base = walkExpr(targetStmt.lhs.base, false)
            targetStmt.lhs.index = walkExpr(targetStmt.lhs.index, false)
            passedImpure = true
        end
        targetStmt.rhs = walkExpr(targetStmt.rhs, false)
    end

    return replaced and not aborted
end

function Passes.resynthesizeLogic(ast)
    local anyChanged = false

    local hasWeakMode = false
    visitast(ast, function(n)
        if n.kind == AstKind.StringExpression and n.value == "__mode" then
            hasWeakMode = true
        end
    end)

    for round = 1, 10 do
        local roundChanged = false
        local capturedRead, capturedWrite = collectClosureCaptures(ast)
        local reads, writes = countVarUsage(ast)

        local tonumberVars = {}
        local errorVars = {}
        visitast(ast, function(n)
            if n.kind == AstKind.LocalVariableDeclaration and #n.ids == 1 and n.expressions and #n.expressions == 1 then
                local k = varKey(n.scope, n.ids[1])
                if (writes[k] or 0) == 1 and not capturedWrite[k] then
                    if isGlobalVar(n.expressions[1], "tonumber") then
                        tonumberVars[k] = true
                    elseif isGlobalVar(n.expressions[1], "error") then
                        errorVars[k] = true
                    end
                end
            end
        end)

        local preLoopBlocks = {}
        visitast(ast, function(n)
            if n.kind == AstKind.Block then
                preLoopBlocks[#preLoopBlocks + 1] = n
            end
        end)

        for bIdx = #preLoopBlocks, 1, -1 do
            if reconstructCffLoopsInBlock(preLoopBlocks[bIdx], capturedRead, tonumberVars, errorVars, ast.globalScope) then
                roundChanged = true
            end
        end

        if roundChanged then
            capturedRead, capturedWrite = collectClosureCaptures(ast)
            reads, writes = countVarUsage(ast)
        end

        local allBlocks = {}
        local funcRootBlocks = { [ast.body] = ast.body.scope }
        local loopChildBlocks = {}
        visitast(ast, function(n)
            if n.kind == AstKind.Block then
                allBlocks[#allBlocks + 1] = n
            elseif FUNCTION_KINDS[n.kind] and n.body then
                funcRootBlocks[n.body] = n.body.scope
            elseif (n.kind == AstKind.ForStatement or n.kind == AstKind.ForInStatement
                or n.kind == AstKind.WhileStatement or n.kind == AstKind.RepeatStatement) and n.body then
                loopChildBlocks[n.body] = true
            end
        end)

        for bIdx = #allBlocks, 1, -1 do
            local blk = allBlocks[bIdx]
            local stmts = blk.statements
            local blockDeclaredScopes = { [blk.scope] = true }
            for _, bs in ipairs(stmts) do
                if bs.kind == AstKind.LocalVariableDeclaration and bs.scope then
                    blockDeclaredScopes[bs.scope] = true
                end
            end

            for pIdx = 1, #stmts do
                local sp = stmts[pIdx]
                if isNilAssignStmt(sp) then
                    local nSc, nId = sp.lhs[1].scope, sp.lhs[1].id
                    if not capturedWrite[varKey(nSc, nId)] then
                        for qIdx = pIdx + 1, #stmts do
                            local sq = stmts[qIdx]
                            if sq.kind == AstKind.WhileStatement or sq.kind == AstKind.RepeatStatement
                                or sq.kind == AstKind.ForStatement or sq.kind == AstKind.ForInStatement then
                                break
                            end
                            if sq.kind == AstKind.AssignmentStatement and #sq.lhs == 1
                                and isSameVar(sq.lhs[1], nSc, nId) then
                                sq.rhs[1] = visitNode(sq.rhs[1], function(m)
                                    if FUNCTION_KINDS[m.kind] then return nil, true end
                                end, function(m)
                                    if isVarRef(m, nSc, nId) then
                                        roundChanged = true
                                        return Ast.NilExpression()
                                    end
                                end, ast.globalScope)
                                break
                            end
                            local wroteInside = false
                            visitNode(sq, function(m)
                                if m.kind == AstKind.AssignmentVariable and isSameVar(m, nSc, nId) then
                                    wroteInside = true
                                elseif m.lhs and m.rhs and m.kind ~= AstKind.AssignmentStatement and isSameVar(m.lhs, nSc, nId) then
                                    wroteInside = true
                                end
                            end, nil, ast.globalScope)
                            if wroteInside then
                                if sq.kind == AstKind.IfStatement then
                                    sq.condition = visitNode(sq.condition, function(m)
                                        if FUNCTION_KINDS[m.kind] then return nil, true end
                                    end, function(m)
                                        if isVarRef(m, nSc, nId) then
                                            roundChanged = true
                                            return Ast.NilExpression()
                                        end
                                    end, ast.globalScope)
                                end
                                break
                            end
                            stmts[qIdx] = visitNode(sq, function(m)
                                if FUNCTION_KINDS[m.kind] then return nil, true end
                            end, function(m)
                                if isVarRef(m, nSc, nId) then
                                    roundChanged = true
                                    return Ast.NilExpression()
                                end
                            end, ast.globalScope)
                        end
                    end
                end
            end
            if roundChanged then
                reads, writes = countVarUsage(ast)
            end

            local k = 1
            while k <= #stmts do
                local sk = stmts[k]
                if sk.kind == AstKind.LocalVariableDeclaration and #sk.ids == 3
                    and sk.expressions and #sk.expressions == 1
                    and isMultiReturnExpr(sk.expressions[1]) then
                    local id1, id2, id3 = sk.ids[1], sk.ids[2], sk.ids[3]
                    local k1, k2, k3 = varKey(sk.scope, id1), varKey(sk.scope, id2), varKey(sk.scope, id3)
                    if not capturedRead[k1] and not capturedRead[k2] and not capturedRead[k3]
                        and (writes[k1] or 0) == 1 and (writes[k2] or 0) == 1 and (writes[k3] or 0) == 1 then
                        local aliasMap = {
                            [k1] = 1,
                            [k2] = 2,
                            [k3] = 3,
                        }
                        local aliasStmtIdxs = {}
                        local p = k + 1
                        local pureBetween = true
                        while p <= #stmts and stmts[p].kind ~= AstKind.ForInStatement do
                            local sp = stmts[p]
                            if isNilAssignStmt(sp) then
                                p = p + 1
                            elseif sp.kind == AstKind.LocalVariableDeclaration and #sp.ids == 1
                                and sp.expressions and #sp.expressions == 1
                                and sp.expressions[1].kind == AstKind.VariableExpression then
                                local srcSlot = aliasMap[varKey(sp.expressions[1].scope, sp.expressions[1].id)]
                                local ak = varKey(sp.scope, sp.ids[1])
                                if srcSlot and not capturedRead[ak] and (writes[ak] or 0) == 1 and (reads[ak] or 0) == 1 then
                                    aliasMap[ak] = srcSlot
                                    aliasStmtIdxs[p] = true
                                    p = p + 1
                                elseif not stmtHasObservableEffect(sp, ast.globalScope) then
                                    p = p + 1
                                else
                                    pureBetween = false
                                    break
                                end
                            elseif not stmtHasObservableEffect(sp, ast.globalScope) then
                                p = p + 1
                            else
                                pureBetween = false
                                break
                            end
                        end
                        if pureBetween and p <= #stmts and stmts[p].kind == AstKind.ForInStatement
                            and #stmts[p].expressions == 3 then
                            local e1, e2, e3 = stmts[p].expressions[1], stmts[p].expressions[2], stmts[p].expressions[3]
                            if e1.kind == AstKind.VariableExpression and aliasMap[varKey(e1.scope, e1.id)] == 1
                                and e2.kind == AstKind.VariableExpression and aliasMap[varKey(e2.scope, e2.id)] == 2
                                and e3.kind == AstKind.VariableExpression and aliasMap[varKey(e3.scope, e3.id)] == 3 then
                                local totalAllowedReads = { [k1] = 1, [k2] = 1, [k3] = 1 }
                                for pIdx in pairs(aliasStmtIdxs) do
                                    local srcV = stmts[pIdx].expressions[1]
                                    local skSrc = varKey(srcV.scope, srcV.id)
                                    totalAllowedReads[skSrc] = (totalAllowedReads[skSrc] or 0) + 1
                                end
                                if (reads[k1] or 0) == totalAllowedReads[k1]
                                    and (reads[k2] or 0) == totalAllowedReads[k2]
                                    and (reads[k3] or 0) == totalAllowedReads[k3] then
                                    local callOk = true
                                    for mid = k + 1, p - 1 do
                                        if not aliasStmtIdxs[mid] then
                                            visitNode(stmts[mid], function(n)
                                                if n.kind == AstKind.AssignmentVariable then
                                                    local wk = varKey(n.scope, n.id)
                                                    visitNode(sk.expressions[1], function(m)
                                                        if m.kind == AstKind.VariableExpression and varKey(m.scope, m.id) == wk then
                                                            callOk = false
                                                        end
                                                    end, nil, ast.globalScope)
                                                end
                                            end, nil, ast.globalScope)
                                        end
                                    end
                                    if callOk then
                                        stmts[p].expressions = { sk.expressions[1] }
                                        for rem = p - 1, k + 1, -1 do
                                            if aliasStmtIdxs[rem] then
                                                table.remove(stmts, rem)
                                            end
                                        end
                                        table.remove(stmts, k)
                                        reads, writes = countVarUsage(ast)
                                        roundChanged = true
                                    else
                                        k = k + 1
                                    end
                                else
                                    k = k + 1
                                end
                            else
                                k = k + 1
                            end
                        else
                            k = k + 1
                        end
                    else
                        k = k + 1
                    end
                else
                    k = k + 1
                end
            end

            for idx = #stmts, 1, -1 do
                local s = stmts[idx]
                if s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                    and s.lhs[1].kind == AstKind.AssignmentVariable and not s.lhs[1].scope.isGlobal then
                    local vSc, vId = s.lhs[1].scope, s.lhs[1].id
                    local vk = varKey(vSc, vId)
                    if not capturedRead[vk] then
                        if s.rhs[1].kind == AstKind.TableConstructorExpression and #s.rhs[1].entries == 1
                            and s.rhs[1].entries[1].kind == AstKind.TableEntry
                            and s.rhs[1].entries[1].value.kind == AstKind.VarargExpression
                            and (reads[vk] or 0) == 0 then
                            table.remove(stmts, idx)
                            roundChanged = true
                        elseif s.rhs[1].kind == AstKind.NilExpression then
                            local readBeforeKill = false
                            local killedLater = false
                            local effectBeforeEnd = false
                            for j = idx + 1, #stmts do
                                local sj = stmts[j]
                                if sj.kind == AstKind.AssignmentStatement and #sj.lhs == 1
                                    and sj.lhs[1].kind == AstKind.AssignmentVariable
                                    and sj.lhs[1].scope == vSc and sj.lhs[1].id == vId then
                                    visitNode(sj.rhs[1], function(n)
                                        if isVarRef(n, vSc, vId) then readBeforeKill = true end
                                    end, nil, ast.globalScope)
                                    killedLater = true
                                    break
                                end
                                visitNode(sj, function(n)
                                    if isVarRef(n, vSc, vId) then readBeforeKill = true end
                                end, nil, ast.globalScope)
                                if readBeforeKill then break end
                                if hasWeakMode and stmtHasObservableEffect(sj, ast.globalScope) then
                                    effectBeforeEnd = true
                                end
                            end
                            local endsWithReturn = #stmts >= 1 and stmts[#stmts].kind == AstKind.ReturnStatement
                            local deadAtScopeEnd = (not readBeforeKill) and (not effectBeforeEnd)
                                and ((funcRootBlocks[blk] ~= nil and blockDeclaredScopes[vSc])
                                    or (loopChildBlocks[blk] and blockDeclaredScopes[vSc])
                                    or (endsWithReturn and not hasWeakMode))
                            if (killedLater and not readBeforeKill and (not hasWeakMode or not effectBeforeEnd))
                                or deadAtScopeEnd
                                or ((reads[vk] or 0) == 0 and not hasWeakMode) then
                                table.remove(stmts, idx)
                                roundChanged = true
                            end
                        end
                    end
                elseif s.kind == AstKind.LocalVariableDeclaration then
                    local allUnused = true
                    for _, id in ipairs(s.ids) do
                        local ik = varKey(s.scope, id)
                        if (reads[ik] or 0) > 0 or (writes[ik] or 0) > 1 or capturedRead[ik] then
                            allUnused = false
                            break
                        end
                    end
                    if allUnused then
                        local pureRhs = true
                        if s.expressions then
                            for _, ex in ipairs(s.expressions) do
                                local okEx = ex.kind == AstKind.NilExpression
                                    or ex.kind == AstKind.BooleanExpression
                                    or ex.kind == AstKind.NumberExpression
                                    or ex.kind == AstKind.StringExpression
                                    or ex.kind == AstKind.VariableExpression
                                    or ex.kind == AstKind.FunctionLiteralExpression
                                    or (ex.kind == AstKind.OrExpression
                                        and ex.lhs.kind == AstKind.VariableExpression
                                        and ex.rhs.kind == AstKind.IndexExpression
                                        and ex.rhs.base.kind == AstKind.VariableExpression)
                                    or (not hasWeakMode and ex.kind == AstKind.TableConstructorExpression and #ex.entries == 0)
                                    or (ex.kind == AstKind.TableConstructorExpression and #ex.entries == 1
                                        and ex.entries[1].kind == AstKind.TableEntry
                                        and ex.entries[1].value.kind == AstKind.VarargExpression)
                                if not okEx then pureRhs = false break end
                            end
                        end
                        if pureRhs then
                            table.remove(stmts, idx)
                            roundChanged = true
                        end
                    end
                elseif s.kind == AstKind.LocalFunctionDeclaration then
                    local fk = varKey(s.scope, s.id)
                    local selfReads = 0
                    visitNode(s.body, function(n)
                        if isVarRef(n, s.scope, s.id) then selfReads = selfReads + 1 end
                    end, nil, ast.globalScope)
                    if (reads[fk] or 0) <= selfReads and (writes[fk] or 0) <= 1 then
                        table.remove(stmts, idx)
                        roundChanged = true
                    end
                end
            end

            local scIdx = 1
            while scIdx + 2 <= #stmts do
                local s1, s2 = stmts[scIdx], stmts[scIdx + 1]
                local ifPos = scIdx + 2
                while ifPos <= #stmts and isNilAssignStmt(stmts[ifPos]) do
                    ifPos = ifPos + 1
                end
                local s3 = stmts[ifPos]
                local aSc, aId, aSrc = nil, nil, nil
                if s1.kind == AstKind.AssignmentStatement and #s1.lhs == 1 and #s1.rhs == 1
                    and s1.lhs[1].kind == AstKind.AssignmentVariable and not s1.lhs[1].scope.isGlobal then
                    aSc, aId, aSrc = s1.lhs[1].scope, s1.lhs[1].id, s1.rhs[1]
                elseif s1.kind == AstKind.LocalVariableDeclaration and #s1.ids == 1
                    and s1.expressions and #s1.expressions == 1 then
                    aSc, aId, aSrc = s1.scope, s1.ids[1], s1.expressions[1]
                end
                local bSc, bId, bSrc = nil, nil, nil
                if s2.kind == AstKind.AssignmentStatement and #s2.lhs == 1 and #s2.rhs == 1
                    and s2.lhs[1].kind == AstKind.AssignmentVariable and not s2.lhs[1].scope.isGlobal then
                    bSc, bId, bSrc = s2.lhs[1].scope, s2.lhs[1].id, s2.rhs[1]
                elseif s2.kind == AstKind.LocalVariableDeclaration and #s2.ids == 1
                    and s2.expressions and #s2.expressions == 1 then
                    bSc, bId, bSrc = s2.scope, s2.ids[1], s2.expressions[1]
                end
                if aSc and bSc and s3
                    and aSrc.kind == AstKind.VariableExpression and not aSrc.scope.isGlobal
                    and isVarRef(bSrc, aSrc.scope, aSrc.id)
                    and s3.kind == AstKind.IfStatement and #s3.elseifs == 0
                    and (not s3.elsebody or #s3.elsebody.statements == 0) then
                    local resSc, resId, condSc, condId, condStmtIdx = nil, nil, nil, nil, nil
                    if isVarRef(s3.condition, bSc, bId)
                        or (s3.condition.kind == AstKind.NotExpression and isVarRef(s3.condition.rhs, bSc, bId)) then
                        resSc, resId, condSc, condId, condStmtIdx = aSc, aId, bSc, bId, scIdx + 1
                    elseif isVarRef(s3.condition, aSc, aId)
                        or (s3.condition.kind == AstKind.NotExpression and isVarRef(s3.condition.rhs, aSc, aId)) then
                        resSc, resId, condSc, condId, condStmtIdx = bSc, bId, aSc, aId, scIdx
                    end
                    local nilClobbered = false
                    if condSc then
                        for np = scIdx + 2, ifPos - 1 do
                            if isSameVar(stmts[np].lhs[1], resSc, resId) or isSameVar(stmts[np].lhs[1], condSc, condId) then
                                nilClobbered = true
                            end
                        end
                    end
                    if condSc and not nilClobbered then
                        local ck = varKey(condSc, condId)
                        local rk = varKey(resSc, resId)
                        local condIsPos = isVarRef(s3.condition, condSc, condId)
                        local condIsNeg = (s3.condition.kind == AstKind.NotExpression and isVarRef(s3.condition.rhs, condSc, condId))
                        if (condIsPos or condIsNeg) and not capturedRead[ck] and not capturedRead[rk]
                            and (reads[ck] or 0) == 1 then
                            local resReadInBody = false
                            local condTouchedInBody = false
                            visitNode(s3.body, function(n)
                                if isSameVar(n, condSc, condId) then condTouchedInBody = true end
                            end, nil, ast.globalScope)
                            local lastNonNilIdx = #s3.body.statements
                            while lastNonNilIdx >= 1 and isNilAssignStmt(s3.body.statements[lastNonNilIdx])
                                and not isSameVar(s3.body.statements[lastNonNilIdx].lhs[1], resSc, resId) do
                                lastNonNilIdx = lastNonNilIdx - 1
                            end
                            if lastNonNilIdx >= 1 then
                                for q = 1, lastNonNilIdx do
                                    local bsq = s3.body.statements[q]
                                    if q == lastNonNilIdx and bsq.kind == AstKind.AssignmentStatement
                                        and #bsq.lhs == 1 and isSameVar(bsq.lhs[1], resSc, resId) then
                                        visitNode(bsq.rhs[1], function(n)
                                            if isVarRef(n, resSc, resId) then resReadInBody = true end
                                        end, nil, ast.globalScope)
                                    else
                                        visitNode(bsq, function(n)
                                            if isVarRef(n, resSc, resId) then resReadInBody = true end
                                        end, nil, ast.globalScope)
                                    end
                                end
                            end
                            if not condTouchedInBody and not resReadInBody then
                                if condIsPos then
                                    s3.condition = Ast.VariableExpression(resSc, resId)
                                else
                                    s3.condition = Ast.NotExpression(Ast.VariableExpression(resSc, resId))
                                end
                                for rem = ifPos - 1, scIdx + 2, -1 do
                                    if not hasWeakMode then
                                        table.remove(stmts, rem)
                                    end
                                end
                                table.remove(stmts, condStmtIdx)
                                reads, writes = countVarUsage(ast)
                                roundChanged = true
                            else
                                scIdx = scIdx + 1
                            end
                        else
                            scIdx = scIdx + 1
                        end
                    else
                        scIdx = scIdx + 1
                    end
                else
                    scIdx = scIdx + 1
                end
            end

            scIdx = 1
            while scIdx + 1 <= #stmts do
                local s1 = stmts[scIdx]
                local ifPos2 = scIdx + 1
                while ifPos2 <= #stmts and isNilAssignStmt(stmts[ifPos2]) do
                    ifPos2 = ifPos2 + 1
                end
                local s2 = stmts[ifPos2]
                local resSc, resId, lhsExpr, isLocalInit = nil, nil, nil, false
                if s1.kind == AstKind.AssignmentStatement and #s1.lhs == 1 and #s1.rhs == 1
                    and s1.lhs[1].kind == AstKind.AssignmentVariable and not s1.lhs[1].scope.isGlobal then
                    resSc, resId, lhsExpr, isLocalInit = s1.lhs[1].scope, s1.lhs[1].id, s1.rhs[1], false
                elseif s1.kind == AstKind.LocalVariableDeclaration and #s1.ids == 1
                    and s1.expressions and #s1.expressions == 1 then
                    resSc, resId, lhsExpr, isLocalInit = s1.scope, s1.ids[1], s1.expressions[1], true
                end
                local nilHitRes = false
                if resSc then
                    for np = scIdx + 1, ifPos2 - 1 do
                        if isSameVar(stmts[np].lhs[1], resSc, resId) then nilHitRes = true end
                    end
                end
                if resSc and not nilHitRes and s2 and not capturedRead[varKey(resSc, resId)]
                    and s2.kind == AstKind.IfStatement and #s2.elseifs == 0
                    and (not s2.elsebody or #s2.elsebody.statements == 0)
                    and #s2.body.statements == 1 then
                    local innerS = s2.body.statements[1]
                    if innerS.kind == AstKind.AssignmentStatement and #innerS.lhs == 1 and #innerS.rhs == 1
                        and isSameVar(innerS.lhs[1], resSc, resId) then
                        local condPos = isVarRef(s2.condition, resSc, resId)
                        local condNeg = (s2.condition.kind == AstKind.NotExpression and isVarRef(s2.condition.rhs, resSc, resId))
                        if condPos or condNeg then
                            local rhsSelfRead = false
                            visitNode(innerS.rhs[1], function(n)
                                if isVarRef(n, resSc, resId) then rhsSelfRead = true end
                            end, nil, ast.globalScope)
                            if not rhsSelfRead then
                                local combined = condPos
                                    and Ast.AndExpression(lhsExpr, innerS.rhs[1])
                                    or Ast.OrExpression(lhsExpr, innerS.rhs[1])
                                if isLocalInit then
                                    stmts[scIdx] = Ast.LocalVariableDeclaration(resSc, { resId }, { combined })
                                else
                                    stmts[scIdx] = Ast.AssignmentStatement({ Ast.AssignmentVariable(resSc, resId) }, { combined })
                                end
                                for rem = ifPos2, scIdx + 1, -1 do
                                    if rem == ifPos2 or not hasWeakMode then
                                        table.remove(stmts, rem)
                                    end
                                end
                                reads, writes = countVarUsage(ast)
                                roundChanged = true
                            else
                                scIdx = scIdx + 1
                            end
                        else
                            scIdx = scIdx + 1
                        end
                    else
                        scIdx = scIdx + 1
                    end
                else
                    scIdx = scIdx + 1
                end
            end

            local aIdx = 1
            while aIdx <= #stmts do
                local sa = stmts[aIdx]
                if sa.kind == AstKind.LocalVariableDeclaration and #sa.ids == 1
                    and sa.expressions and #sa.expressions == 1
                    and sa.expressions[1].kind == AstKind.VariableExpression
                    and not sa.expressions[1].scope.isGlobal then
                    local dstSc, dstId = sa.scope, sa.ids[1]
                    local srcSc, srcId = sa.expressions[1].scope, sa.expressions[1].id
                    local dk, sk2 = varKey(dstSc, dstId), varKey(srcSc, srcId)
                    if (dk ~= sk2) and dstSc == srcSc
                        and (writes[dk] or 0) == 1 and not capturedRead[dk]
                        and (writes[sk2] or 0) == 0 and not capturedWrite[sk2] then
                        local srcLoopMutated = false
                        visitast(ast, function(n)
                            if n.kind == AstKind.ForStatement and n.scope == srcSc and n.id == srcId then
                                srcLoopMutated = true
                            elseif n.kind == AstKind.ForInStatement and n.scope == srcSc then
                                for _, lid in ipairs(n.ids) do
                                    if lid == srcId then srcLoopMutated = true end
                                end
                            elseif n.lhs and n.rhs and n.kind ~= AstKind.AssignmentStatement
                                and isSameVar(n.lhs, srcSc, srcId) then
                                srcLoopMutated = true
                            elseif n.lhs and n.rhs and n.kind ~= AstKind.AssignmentStatement
                                and isSameVar(n.lhs, dstSc, dstId) then
                                srcLoopMutated = true
                            end
                        end)
                        if not srcLoopMutated then
                            for m = aIdx + 1, #stmts do
                                stmts[m] = visitNode(stmts[m], nil, function(n)
                                    if isVarRef(n, dstSc, dstId) then
                                        return Ast.VariableExpression(srcSc, srcId)
                                    end
                                end, ast.globalScope)
                            end
                            table.remove(stmts, aIdx)
                            reads, writes = countVarUsage(ast)
                            roundChanged = true
                        else
                            aIdx = aIdx + 1
                        end
                    else
                        aIdx = aIdx + 1
                    end
                else
                    aIdx = aIdx + 1
                end
            end

            reads, writes = countVarUsage(ast)

            for idx = #stmts - 1, 1, -1 do
                local s = stmts[idx]
                local vSc, vId, rhs, isLocalDecl, keepEmptyDecl = nil, nil, nil, false, false
                if s.kind == AstKind.LocalVariableDeclaration and #s.ids == 1
                    and s.expressions and #s.expressions == 1 then
                    local k = varKey(s.scope, s.ids[1])
                    if not capturedRead[k] then
                        if (reads[k] or 0) == 1 and (writes[k] or 0) == 1 then
                            vSc, vId, rhs, isLocalDecl, keepEmptyDecl = s.scope, s.ids[1], s.expressions[1], true, false
                        else
                            vSc, vId, rhs, isLocalDecl, keepEmptyDecl = s.scope, s.ids[1], s.expressions[1], false, true
                        end
                    end
                elseif s.kind == AstKind.AssignmentStatement and #s.lhs == 1 and #s.rhs == 1
                    and s.lhs[1].kind == AstKind.AssignmentVariable and not s.lhs[1].scope.isGlobal
                    and s.rhs[1].kind ~= AstKind.NilExpression then
                    local k = varKey(s.lhs[1].scope, s.lhs[1].id)
                    if not capturedRead[k] then
                        local selfRef = false
                        visitNode(s.rhs[1], function(n)
                            if isVarRef(n, s.lhs[1].scope, s.lhs[1].id) then selfRef = true end
                        end, nil, ast.globalScope)
                        if not selfRef then
                            vSc, vId, rhs, isLocalDecl, keepEmptyDecl = s.lhs[1].scope, s.lhs[1].id, s.rhs[1], false, false
                        end
                    end
                end

                if vSc and rhs and not (hasWeakMode and rhs.kind == AstKind.TableConstructorExpression and #rhs.entries == 0) then
                    local vkInline = varKey(vSc, vId)
                    local readIdx = nil
                    local totalReadsForward = 0
                    local killedAfter = isLocalDecl or ((reads[vkInline] or 0) == 1 and (writes[vkInline] or 0) == 1)
                    local killStmtIdx = nil
                    local unsafeSpan = false

                    for j = idx + 1, #stmts do
                        local sj = stmts[j]
                        if sj.kind == AstKind.AssignmentStatement and #sj.lhs == 1
                            and sj.lhs[1].kind == AstKind.AssignmentVariable
                            and sj.lhs[1].scope == vSc and sj.lhs[1].id == vId then
                            local rc = 0
                            visitNode(sj.rhs[1], function(n)
                                if isVarRef(n, vSc, vId) then rc = rc + 1 end
                            end, nil, ast.globalScope)
                            if rc > 0 then
                                totalReadsForward = totalReadsForward + rc
                                readIdx = readIdx or j
                            end
                            if readIdx then
                                killedAfter = true
                                if sj.rhs[1].kind == AstKind.NilExpression and j > readIdx then
                                    killStmtIdx = j
                                end
                            else
                                unsafeSpan = true
                            end
                            break
                        else
                            local rc = 0
                            local readInLoopOrClosure = false
                            local wroteTargetInside = false
                            visitNode(sj, function(n)
                                if n.kind == AstKind.AssignmentVariable and isSameVar(n, vSc, vId) then
                                    wroteTargetInside = true
                                elseif n.lhs and n.rhs and n.kind ~= AstKind.AssignmentStatement and isSameVar(n.lhs, vSc, vId) then
                                    wroteTargetInside = true
                                end
                                if (n.kind == AstKind.WhileStatement or n.kind == AstKind.RepeatStatement
                                    or FUNCTION_KINDS[n.kind]) then
                                    visitNode(n, function(m)
                                        if isSameVar(m, vSc, vId) then
                                            rc = rc + 2
                                            readInLoopOrClosure = true
                                        end
                                    end, nil, ast.globalScope)
                                    return nil, true
                                end
                                if (n.kind == AstKind.ForStatement or n.kind == AstKind.ForInStatement) and n.body then
                                    visitNode(n.body, function(m)
                                        if isSameVar(m, vSc, vId) then
                                            rc = rc + 2
                                            readInLoopOrClosure = true
                                        end
                                    end, nil, ast.globalScope)
                                    if n.kind == AstKind.ForStatement then
                                        if isVarRef(n.initialValue, vSc, vId) then rc = rc + 1 end
                                        if isVarRef(n.finalValue, vSc, vId) then rc = rc + 1 end
                                        if n.incrementBy and isVarRef(n.incrementBy, vSc, vId) then rc = rc + 1 end
                                        visitNode(n.initialValue, function(m) if m ~= n.initialValue and isVarRef(m, vSc, vId) then rc = rc + 1 end end, nil, ast.globalScope)
                                        visitNode(n.finalValue, function(m) if m ~= n.finalValue and isVarRef(m, vSc, vId) then rc = rc + 1 end end, nil, ast.globalScope)
                                        if n.incrementBy then
                                            visitNode(n.incrementBy, function(m) if m ~= n.incrementBy and isVarRef(m, vSc, vId) then rc = rc + 1 end end, nil, ast.globalScope)
                                        end
                                    else
                                        for _, ex in ipairs(n.expressions) do
                                            visitNode(ex, function(m) if isVarRef(m, vSc, vId) then rc = rc + 1 end end, nil, ast.globalScope)
                                        end
                                    end
                                    return nil, true
                                end
                                if isVarRef(n, vSc, vId) then rc = rc + 1 end
                            end, nil, ast.globalScope)
                            if readInLoopOrClosure or wroteTargetInside then
                                unsafeSpan = true
                                break
                            end
                            if rc > 0 then
                                totalReadsForward = totalReadsForward + rc
                                readIdx = readIdx or j
                            end
                            if not readIdx and (sj.kind == AstKind.WhileStatement or sj.kind == AstKind.RepeatStatement
                                or sj.kind == AstKind.ForStatement or sj.kind == AstKind.ForInStatement) then
                                unsafeSpan = true
                                break
                            end
                        end
                    end

                    if not killedAfter and readIdx and totalReadsForward == 1 then
                        local endsRet = #stmts >= 1 and stmts[#stmts].kind == AstKind.ReturnStatement
                        if funcRootBlocks[blk] ~= nil and blockDeclaredScopes[vSc] then
                            killedAfter = true
                        elseif loopChildBlocks[blk] and blockDeclaredScopes[vSc] then
                            killedAfter = true
                        elseif endsRet and not hasWeakMode then
                            killedAfter = true
                        end
                    end

                    if not unsafeSpan and killedAfter and readIdx and totalReadsForward == 1 then
                        local betweenScopes = {}
                        for m = idx + 1, readIdx - 1 do
                            if stmts[m].kind == AstKind.LocalVariableDeclaration then
                                betweenScopes[stmts[m].scope] = true
                            end
                        end
                        local rhsLocalDeps = {}
                        visitNode(rhs, function(n)
                            if FUNCTION_KINDS[n.kind] then return nil, true end
                            if n.kind == AstKind.VariableExpression and not n.scope.isGlobal then
                                rhsLocalDeps[varKey(n.scope, n.id)] = true
                            end
                        end, nil, ast.globalScope)

                        local rhsIsPure = isPureConstOrFnExpr(rhs, next(betweenScopes) and betweenScopes or nil)
                            or (rhs.kind == AstKind.VariableExpression and not rhs.scope.isGlobal
                                and not capturedWrite[varKey(rhs.scope, rhs.id)])

                        local spanSafe = true
                        for m = idx + 1, readIdx - 1 do
                            local sm = stmts[m]
                            visitNode(sm, function(n)
                                if n.kind == AstKind.AssignmentVariable and rhsLocalDeps[varKey(n.scope, n.id)] then
                                    spanSafe = false
                                end
                            end, nil, ast.globalScope)
                            if not rhsIsPure and stmtHasObservableEffect(sm, ast.globalScope) then
                                spanSafe = false
                            end
                            if not spanSafe then break end
                        end

                        if spanSafe then
                            local needsSingleVal = isMultiReturnExpr(rhs)
                            if tryInlineIntoStmt(stmts[readIdx], vSc, vId, rhs, rhsIsPure, needsSingleVal) then
                                if killStmtIdx and not hasWeakMode then
                                    table.remove(stmts, killStmtIdx)
                                end
                                if keepEmptyDecl then
                                    stmts[idx] = Ast.LocalVariableDeclaration(vSc, { vId }, {})
                                else
                                    table.remove(stmts, idx)
                                end
                                reads, writes = countVarUsage(ast)
                                roundChanged = true
                            end
                        end
                    end
                end
            end
        end

        local capturedRead2 = collectClosureCaptures(ast)
        local reads2, writes2 = countVarUsage(ast)
        visitast(ast, function(blk)
            if blk.kind ~= AstKind.Block then return end
            local stmts = blk.statements
            local declIdxs = {}
            local uninitEntries = {}
            for idx = 1, #stmts do
                local s = stmts[idx]
                if s.kind == AstKind.LocalVariableDeclaration and (not s.expressions or #s.expressions == 0) then
                    declIdxs[#declIdxs + 1] = idx
                    for _, id in ipairs(s.ids) do
                        local uk = varKey(s.scope, id)
                        if not uninitEntries[uk] then
                            uninitEntries[uk] = { scope = s.scope, id = id, declIdx = idx }
                        end
                    end
                elseif s.kind ~= AstKind.LocalVariableDeclaration and s.kind ~= AstKind.LocalFunctionDeclaration then
                    break
                end
            end
            if next(uninitEntries) == nil then return end

            local promotedKeys = {}
            for uk, infoU in pairs(uninitEntries) do
                local uSc, uId, dIdx = infoU.scope, infoU.id, infoU.declIdx
                if (reads2[uk] or 0) == 0 and (writes2[uk] or 0) == 0 and not capturedRead2[uk] then
                    promotedKeys[uk] = true
                else
                    local firstStmtIdx = nil
                    for idx = 1, #stmts do
                        if idx ~= dIdx then
                            local hit = false
                            visitNode(stmts[idx], function(n)
                                if isSameVar(n, uSc, uId) then hit = true end
                            end, nil, ast.globalScope)
                            if hit then
                                firstStmtIdx = idx
                                break
                            end
                        end
                    end
                    if firstStmtIdx and firstStmtIdx > dIdx then
                        local fs = stmts[firstStmtIdx]
                        if fs.kind == AstKind.AssignmentStatement and #fs.lhs == 1 and #fs.rhs == 1
                            and fs.lhs[1].kind == AstKind.AssignmentVariable
                            and fs.lhs[1].scope == uSc and fs.lhs[1].id == uId then
                            local rhs = fs.rhs[1]
                            if rhs.kind == AstKind.FunctionLiteralExpression and (writes2[uk] or 0) == 1 then
                                stmts[firstStmtIdx] = Ast.LocalFunctionDeclaration(uSc, uId, rhs.args, rhs.body)
                                promotedKeys[uk] = true
                            elseif rhs.kind ~= AstKind.FunctionLiteralExpression then
                                local selfRef = false
                                visitNode(rhs, function(n)
                                    if isSameVar(n, uSc, uId) then selfRef = true end
                                end, nil, ast.globalScope)
                                if not selfRef then
                                    stmts[firstStmtIdx] = Ast.LocalVariableDeclaration(uSc, { uId }, { rhs })
                                    promotedKeys[uk] = true
                                end
                            end
                        end
                    end
                end
            end

            if next(promotedKeys) ~= nil then
                for d = #declIdxs, 1, -1 do
                    local dIdx = declIdxs[d]
                    local ds = stmts[dIdx]
                    local kept = {}
                    for _, id in ipairs(ds.ids) do
                        if not promotedKeys[varKey(ds.scope, id)] then
                            kept[#kept + 1] = id
                        end
                    end
                    if #kept == 0 then
                        table.remove(stmts, dIdx)
                    else
                        ds.ids = kept
                    end
                end
                roundChanged = true
            end
        end)

        if roundChanged then
            anyChanged = true
        else
            break
        end
    end

    return anyChanged
end

return Passes

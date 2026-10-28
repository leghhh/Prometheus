local Parser = require("prometheus.parser")
local Formatter = require("prometheus.formatter")
local Enums = require("prometheus.enums")
local Logger = require("logger")
local visitast = require("prometheus.visitast")
local Ast = require("prometheus.ast")
local Passes = require("prometheus.deobfuscate.passes")
local CffDecompiler = require("prometheus.deobfuscate.cff")
local VmDecompiler = require("prometheus.deobfuscate.vm")

local AstKind = Ast.AstKind
local LuaVersion = Enums.LuaVersion

local Deobfuscator = {}
Deobfuscator.__index = Deobfuscator

local PASS_LIST = {
    {
        name = "FoldConstants",
        run = function(ast)
            return Passes.foldConstants(ast)
        end,
    },
    {
        name = "UnwrapFunction",
        run = function(ast)
            return Passes.unwrapFunction(ast)
        end,
    },
    {
        name = "ResolveConstantArray",
        run = function(ast)
            return Passes.resolveConstantArray(ast)
        end,
    },
    {
        name = "RemoveAntiTamper",
        run = function(ast)
            return Passes.removeAntiTamper(ast)
        end,
    },
    {
        name = "RemoveWatermarks",
        run = function(ast)
            return Passes.removeWatermarks(ast)
        end,
    },
    {
        name = "DecryptStrings",
        run = function(ast)
            return Passes.decryptStrings(ast)
        end,
    },
    {
        name = "UnsplitStrings",
        run = function(ast)
            return Passes.unsplitStrings(ast)
        end,
    },
    {
        name = "UnproxifyLocals",
        run = function(ast)
            return Passes.unproxifyLocals(ast)
        end,
    },
    {
        name = "UnflattenControlFlow",
        run = function(ast, targetVer)
            return CffDecompiler.unflatten(ast, targetVer)
        end,
    },
    {
        name = "SimplifyCells",
        run = function(ast, _, passCounts)
            if not passCounts or not passCounts["UnflattenControlFlow"] or passCounts["LiftVmBytecode"] then
                return false
            end
            return Passes.simplifyCells(ast)
        end,
    },
    {
        name = "UnwrapFlattenVmBridge",
        run = function(ast)
            return Passes.unwrapFlattenVmBridge(ast)
        end,
    },
    {
        name = "LiftVmBytecode",
        run = function(ast, targetVer)
            return VmDecompiler.decompile(ast, targetVer)
        end,
    },
    {
        name = "RemoveAddedVarargs",
        run = function(ast)
            return Passes.removeAddedVarargs(ast)
        end,
    },
}

local function isSyntheticOrMangledName(name)
    if type(name) ~= "string" or #name == 0 then
        return true
    end
    if string.sub(name, 1, 13) == "__prometheus_" then
        return true
    end
    if string.match(name, "^_%d+$") then
        return true
    end
    if #name >= 5 and string.match(name, "^[Il][Il10_]+$") then
        return true
    end
    return false
end

local function normalizeIdentifiers(ast, targetLuaVersion, hadStructuralPasses)
    local keywords = {}
    local conv = Enums.Conventions[targetLuaVersion] or Enums.Conventions[LuaVersion.Lua51]
    for _, kw in ipairs(conv.Keywords) do
        keywords[kw] = true
    end

    local liveScopes = {}
    local liveScopeSet = {}
    local scopeStack = { ast.globalScope }
    local paramVars = {}
    local funcVars = {}
    local referencedInSubtree = {}

    local function ensureScopeTracked(sc)
        if sc and not sc.isGlobal and not liveScopeSet[sc] then
            liveScopeSet[sc] = true
            liveScopes[#liveScopes + 1] = sc
            referencedInSubtree[sc] = {}
            sc.variablesFromHigherScopes = {}
            sc.referenceCounts = {}
        end
    end

    local function markVarRole(tbl, sc, id)
        if not sc or sc.isGlobal then return end
        if not tbl[sc] then tbl[sc] = {} end
        tbl[sc][id] = true
    end

    local function recordHigherRef(declScope, id)
        for idx = #scopeStack, 1, -1 do
            local cur = scopeStack[idx]
            if cur == declScope or cur.isGlobal then
                break
            end
            ensureScopeTracked(cur)
            if not referencedInSubtree[cur][declScope] then
                referencedInSubtree[cur][declScope] = {}
            end
            referencedInSubtree[cur][declScope][id] = true
        end
    end

    visitast(ast, function(node)
        if node.kind == AstKind.Block and node.scope then
            ensureScopeTracked(node.scope)
            if scopeStack[#scopeStack] ~= node.scope then
                node.scope:setParent(scopeStack[#scopeStack])
            end
            scopeStack[#scopeStack + 1] = node.scope
        elseif node.kind == AstKind.ForStatement and node.scope then
            ensureScopeTracked(node.scope)
            if scopeStack[#scopeStack] ~= node.scope then
                node.scope:setParent(scopeStack[#scopeStack])
            end
            scopeStack[#scopeStack + 1] = node.scope
        elseif node.kind == AstKind.ForInStatement and node.scope then
            ensureScopeTracked(node.scope)
            if scopeStack[#scopeStack] ~= node.scope then
                node.scope:setParent(scopeStack[#scopeStack])
            end
            scopeStack[#scopeStack + 1] = node.scope
        elseif node.kind == AstKind.FunctionLiteralExpression
            or node.kind == AstKind.LocalFunctionDeclaration
            or node.kind == AstKind.FunctionDeclaration then
            if node.kind == AstKind.LocalFunctionDeclaration then
                ensureScopeTracked(node.scope)
                markVarRole(funcVars, node.scope, node.id)
                recordHigherRef(node.scope, node.id)
            elseif node.kind == AstKind.FunctionDeclaration and node.scope then
                recordHigherRef(node.scope, node.id)
            end
            for _, arg in ipairs(node.args or {}) do
                if arg.kind == AstKind.VariableExpression and arg.scope then
                    ensureScopeTracked(arg.scope)
                    markVarRole(paramVars, arg.scope, arg.id)
                end
            end
        elseif node.kind == AstKind.LocalVariableDeclaration and node.scope then
            ensureScopeTracked(node.scope)
        elseif (node.kind == AstKind.VariableExpression or node.kind == AstKind.AssignmentVariable) and node.scope then
            if not node.scope.isGlobal then
                ensureScopeTracked(node.scope)
            end
            recordHigherRef(node.scope, node.id)
        end
    end, function(node)
        if (node.kind == AstKind.Block or node.kind == AstKind.ForStatement or node.kind == AstKind.ForInStatement)
            and node.scope and scopeStack[#scopeStack] == node.scope then
            table.remove(scopeStack)
        end
    end)

    local hasSynthetic = false
    local totalLocals = 0
    local shortOrConfuseCount = 0
    for _, sc in ipairs(liveScopes) do
        for id = 1, #sc.variables do
            local nm = sc.variables[id]
            if nm and not sc.skipIdLookup[id] then
                totalLocals = totalLocals + 1
                if isSyntheticOrMangledName(nm) then
                    hasSynthetic = true
                elseif #nm <= 2 or string.find(nm, "_", 1, true) then
                    shortOrConfuseCount = shortOrConfuseCount + 1
                end
            end
        end
    end

    if not hadStructuralPasses and not hasSynthetic then
        return false
    end

    local renameAll = false
    if hadStructuralPasses and totalLocals > 0 and (shortOrConfuseCount == totalLocals) then
        renameAll = true
    end

    local anyRenamed = false
    for _, sc in ipairs(liveScopes) do
        local forbidden = {}
        for kw in pairs(keywords) do
            forbidden[kw] = true
        end
        for refScope, ids in pairs(referencedInSubtree[sc] or {}) do
            for refId in pairs(ids) do
                local refName = refScope:getVariableName(refId)
                if refName then
                    forbidden[refName] = true
                end
            end
        end

        local curScope = sc.parentScope
        while curScope and not curScope.isGlobal do
            for id = 1, #curScope.variables do
                local nm = curScope.variables[id]
                if nm then forbidden[nm] = true end
            end
            curScope = curScope.parentScope
        end

        for id = 1, #sc.variables do
            local nm = sc.variables[id]
            if nm and not sc.skipIdLookup[id] then
                local needRename = renameAll or isSyntheticOrMangledName(nm)
                if not needRename and not forbidden[nm] then
                    forbidden[nm] = true
                end
            end
        end

        sc.variablesLookup = {}
        local pIdx, fIdx, vIdx = 1, 1, 1

        for id = 1, #sc.variables do
            local nm = sc.variables[id]
            if nm and not sc.skipIdLookup[id] then
                local needRename = renameAll or isSyntheticOrMangledName(nm) or (forbidden[nm] and sc.variablesLookup[nm] ~= nil)
                if needRename then
                    local chosen
                    if paramVars[sc] and paramVars[sc][id] then
                        repeat
                            chosen = "p" .. tostring(pIdx)
                            pIdx = pIdx + 1
                        until not forbidden[chosen]
                    elseif funcVars[sc] and funcVars[sc][id] then
                        repeat
                            chosen = "fn" .. tostring(fIdx)
                            fIdx = fIdx + 1
                        until not forbidden[chosen]
                    else
                        repeat
                            chosen = "v" .. tostring(vIdx)
                            vIdx = vIdx + 1
                        until not forbidden[chosen]
                    end
                    if chosen ~= nm then
                        anyRenamed = true
                    end
                    sc.variables[id] = chosen
                    sc.variablesLookup[chosen] = id
                    forbidden[chosen] = true
                else
                    sc.variablesLookup[nm] = id
                    forbidden[nm] = true
                end
            end
        end
    end

    return anyRenamed
end

function Deobfuscator:new(options)
    options = options or {}
    local instance = {
        luaVersion = options.LuaVersion or "Auto",
        targetLuaVersion = options.TargetLuaVersion or nil,
        normalizeIdentifiers = options.NormalizeIdentifiers ~= false,
        maxIterations = options.MaxIterations or 16,
    }
    return setmetatable(instance, Deobfuscator)
end

function Deobfuscator:parseSource(source)
    if type(source) ~= "string" then
        error("Expected source string, got " .. type(source), 0)
    end

    local savedLevel = Logger.logLevel
    local savedErrCb = Logger.errorCallback
    Logger.logLevel = Logger.LogLevel.Error
    Logger.errorCallback = function(msg)
        error(tostring(msg), 0)
    end

    local function tryParse(ver)
        local parser = Parser:new({
            LuaVersion = ver,
            AllowInternalIdentifiers = true,
        })
        return parser:parse(#source == 0 and "\n" or source)
    end

    local ok, astOrErr, detectedVer
    if self.luaVersion == LuaVersion.Lua51 or self.luaVersion == "Lua51" then
        ok, astOrErr = pcall(tryParse, LuaVersion.Lua51)
        detectedVer = LuaVersion.Lua51
    elseif self.luaVersion == LuaVersion.LuaU or self.luaVersion == "LuaU" then
        ok, astOrErr = pcall(tryParse, LuaVersion.LuaU)
        detectedVer = LuaVersion.LuaU
    else
        ok, astOrErr = pcall(tryParse, LuaVersion.Lua51)
        if ok then
            detectedVer = LuaVersion.Lua51
        else
            local okU, astU = pcall(tryParse, LuaVersion.LuaU)
            if okU then
                ok, astOrErr = true, astU
                detectedVer = LuaVersion.LuaU
            end
        end
    end

    Logger.logLevel = savedLevel
    Logger.errorCallback = savedErrCb

    if not ok then
        error(tostring(astOrErr), 0)
    end

    return astOrErr, detectedVer
end

function Deobfuscator:deobfuscateAst(ast, detectedVer)
    local targetVer = self.targetLuaVersion or detectedVer or LuaVersion.Lua51
    local savedLevel = Logger.logLevel
    Logger.logLevel = Logger.LogLevel.Error

    local appliedPasses = {}
    local passCounts = {}
    local iterations = 0
    local hadStructuralPasses = false

    local okRun, runErr = pcall(function()
        for iter = 1, self.maxIterations do
            local iterChanged = false
            for _, pass in ipairs(PASS_LIST) do
                local changed = pass.run(ast, targetVer, passCounts)
                if changed then
                    iterChanged = true
                    if pass.name ~= "FoldConstants" then
                        hadStructuralPasses = true
                    end
                    if not passCounts[pass.name] then
                        passCounts[pass.name] = 0
                        appliedPasses[#appliedPasses + 1] = pass.name
                    end
                    passCounts[pass.name] = passCounts[pass.name] + 1
                end
            end
            if iterChanged then
                iterations = iter
            else
                break
            end
        end

        if self.normalizeIdentifiers then
            local renamed = normalizeIdentifiers(ast, targetVer, hadStructuralPasses)
            if renamed then
                if not passCounts["NormalizeIdentifiers"] then
                    passCounts["NormalizeIdentifiers"] = 0
                    appliedPasses[#appliedPasses + 1] = "NormalizeIdentifiers"
                end
                passCounts["NormalizeIdentifiers"] = passCounts["NormalizeIdentifiers"] + 1
            end
        end
    end)

    Logger.logLevel = savedLevel
    if not okRun then
        error(tostring(runErr), 0)
    end

    return {
        luaVersion = targetVer,
        iterations = iterations,
        appliedPasses = appliedPasses,
        passCounts = passCounts,
    }
end

function Deobfuscator:deobfuscate(source)
    local ast, detectedVer = self:parseSource(source)
    local targetVer = self.targetLuaVersion or detectedVer or LuaVersion.Lua51
    local report = self:deobfuscateAst(ast, detectedVer)
    local formatter = Formatter:new({ LuaVersion = targetVer })
    local output = formatter:format(ast)
    return output, report
end

return Deobfuscator

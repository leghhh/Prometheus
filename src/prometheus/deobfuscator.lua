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

local Detector = {}

function Detector.scan(ast)
    local sig = Passes.detectSignatures(ast)
    local cff = CffDecompiler.detect(ast)
    local vm = VmDecompiler.detect(ast)

    local layers = {}
    if sig.wrapInFunction then layers[#layers + 1] = "WrapInFunction" end
    if sig.packedReturns then layers[#layers + 1] = "PackedReturnBridge" end
    if sig.foldConstants then layers[#layers + 1] = "NumbersToExpressions" end
    if sig.splitStrings then layers[#layers + 1] = "SplitStrings" end
    if sig.proxifyLocals then layers[#layers + 1] = "ProxifyLocals" end
    if sig.constantArray then layers[#layers + 1] = "ConstantArray" end
    if sig.antiTamper then layers[#layers + 1] = "AntiTamper" end
    if sig.watermarks then layers[#layers + 1] = "Watermark" end
    if sig.encryptStrings then layers[#layers + 1] = "EncryptStrings" end
    if cff and cff.present then layers[#layers + 1] = "Cff" end
    if sig.flattenVmBridge then layers[#layers + 1] = "FlattenVmBridge" end
    if vm and vm.present then layers[#layers + 1] = "Vmify" end
    if sig.addedVarargs then layers[#layers + 1] = "AddVararg" end

    local firstPass = nil
    if sig.foldConstants then firstPass = "FoldConstants"
    elseif sig.wrapInFunction or sig.packedReturns then firstPass = "UnwrapFunction"
    elseif sig.splitStrings then firstPass = "UnsplitStrings"
    elseif sig.proxifyLocals then firstPass = "UnproxifyLocals"
    elseif sig.constantArray then firstPass = "ResolveConstantArray"
    elseif sig.antiTamper then firstPass = "RemoveAntiTamper"
    elseif sig.watermarks then firstPass = "RemoveWatermarks"
    elseif sig.encryptStrings then firstPass = "DecryptStrings"
    elseif cff and cff.ready then firstPass = "UnflattenControlFlow"
    elseif sig.flattenVmBridge then firstPass = "UnwrapFlattenVmBridge"
    elseif vm and vm.ready then firstPass = "LiftVmBytecode"
    elseif sig.addedVarargs then firstPass = "RemoveAddedVarargs"
    end

    return {
        isPrometheus = #layers > 0,
        layers = layers,
        recommendedFirstPass = firstPass,
        signatures = sig,
        cff = cff,
        vm = vm,
    }
end

Deobfuscator.Detector = Detector

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
    local usedVars = {}
    local usedOrder = {}
    local referencedInSubtree = {}

    local function ensureScopeTracked(sc)
        if sc and not sc.isGlobal and not liveScopeSet[sc] then
            liveScopeSet[sc] = true
            liveScopes[#liveScopes + 1] = sc
            referencedInSubtree[sc] = {}
            usedVars[sc] = {}
            usedOrder[sc] = {}
            sc.variablesFromHigherScopes = {}
            sc.referenceCounts = {}
        end
    end

    local function markVarUsed(sc, id)
        if not sc or sc.isGlobal or not id then return end
        ensureScopeTracked(sc)
        if not usedVars[sc][id] then
            usedVars[sc][id] = true
            usedOrder[sc][#usedOrder[sc] + 1] = id
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
            markVarUsed(node.scope, node.id)
        elseif node.kind == AstKind.ForInStatement and node.scope then
            ensureScopeTracked(node.scope)
            if scopeStack[#scopeStack] ~= node.scope then
                node.scope:setParent(scopeStack[#scopeStack])
            end
            scopeStack[#scopeStack + 1] = node.scope
            for _, id in ipairs(node.ids or {}) do
                markVarUsed(node.scope, id)
            end
        elseif node.kind == AstKind.FunctionLiteralExpression
            or node.kind == AstKind.LocalFunctionDeclaration
            or node.kind == AstKind.FunctionDeclaration then
            if node.kind == AstKind.LocalFunctionDeclaration then
                markVarUsed(node.scope, node.id)
                markVarRole(funcVars, node.scope, node.id)
                recordHigherRef(node.scope, node.id)
            elseif node.kind == AstKind.FunctionDeclaration and node.scope then
                markVarUsed(node.scope, node.id)
                recordHigherRef(node.scope, node.id)
            end
            for _, arg in ipairs(node.args or {}) do
                if arg.kind == AstKind.VariableExpression and arg.scope then
                    markVarUsed(arg.scope, arg.id)
                    markVarRole(paramVars, arg.scope, arg.id)
                end
            end
        elseif node.kind == AstKind.LocalVariableDeclaration and node.scope then
            ensureScopeTracked(node.scope)
            for _, id in ipairs(node.ids or {}) do
                markVarUsed(node.scope, id)
            end
        elseif (node.kind == AstKind.VariableExpression or node.kind == AstKind.AssignmentVariable) and node.scope then
            if not node.scope.isGlobal then
                markVarUsed(node.scope, node.id)
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
        for _, id in ipairs(usedOrder[sc]) do
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
            local curUsed = usedVars[curScope]
            for id = 1, #curScope.variables do
                if not curUsed or curUsed[id] then
                    local nm = curScope.variables[id]
                    if nm then forbidden[nm] = true end
                end
            end
            curScope = curScope.parentScope
        end

        for _, id in ipairs(usedOrder[sc]) do
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

        for _, id in ipairs(usedOrder[sc]) do
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

function Deobfuscator:detect(source)
    local ast, detectedVer = self:parseSource(source)
    local info = Detector.scan(ast)
    info.luaVersion = detectedVer
    return info
end

function Deobfuscator:deobfuscateAst(ast, detectedVer)
    local targetVer = self.targetLuaVersion or detectedVer or LuaVersion.Lua51
    local savedLevel = Logger.logLevel
    Logger.logLevel = Logger.LogLevel.Error

    local appliedPasses = {}
    local passCounts = {}
    local iterations = 0
    local hadStructuralPasses = false
    local initialDetection = Detector.scan(ast)

    local function recordPass(name)
        if name ~= "FoldConstants" then
            hadStructuralPasses = true
        end
        if not passCounts[name] then
            passCounts[name] = 0
            appliedPasses[#appliedPasses + 1] = name
        end
        passCounts[name] = passCounts[name] + 1
    end

    local function runResynthesis()
        local changed = Passes.unwrapPackedReturns(ast)
        if Passes.resynthesizeLogic(ast) then
            changed = true
            Passes.foldConstants(ast)
            Passes.unwrapPackedReturns(ast)
            Passes.resynthesizeLogic(ast)
        end
        if changed then
            recordPass("ResynthesizeLogic")
        end
        return changed
    end

    local function maybeSimplifyCells()
        if passCounts["UnflattenControlFlow"] and not passCounts["LiftVmBytecode"] then
            if Passes.simplifyCells(ast) then
                recordPass("SimplifyCells")
                return true
            end
        end
        return false
    end

    local function finishUnflatten()
        if Passes.simplifyCells(ast) then
            recordPass("SimplifyCells")
        end
        Passes.unwrapPackedReturns(ast)
        if Passes.unwrapFunction(ast) then
            recordPass("UnwrapFunction")
        end
        if Passes.unwrapFlattenVmBridge(ast) then
            recordPass("UnwrapFlattenVmBridge")
        end
    end

    local settledResynthesis = false

    local okRun, runErr = pcall(function()
        local maxSteps = (self.maxIterations or 16) * 6
        for step = 1, maxSteps do
            local progressed = false

            if Passes.foldConstants(ast) then
                recordPass("FoldConstants")
                progressed = true
            end
            if Passes.unwrapFunction(ast) then
                recordPass("UnwrapFunction")
                progressed = true
            end

            local scan = Detector.scan(ast)
            local sig = scan.signatures

            if sig.splitStrings and Passes.unsplitStrings(ast) then
                recordPass("UnsplitStrings")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif sig.proxifyLocals and Passes.unproxifyLocals(ast) then
                recordPass("UnproxifyLocals")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif sig.constantArray and Passes.resolveConstantArray(ast) then
                recordPass("ResolveConstantArray")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif sig.encryptStrings and Passes.decryptStrings(ast) then
                recordPass("DecryptStrings")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif sig.antiTamper and Passes.removeAntiTamper(ast) then
                recordPass("RemoveAntiTamper")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif sig.watermarks and Passes.removeWatermarks(ast) then
                recordPass("RemoveWatermarks")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif scan.cff and scan.cff.ready and CffDecompiler.unflatten(ast, targetVer) then
                recordPass("UnflattenControlFlow")
                finishUnflatten()
                settledResynthesis = false
                iterations = iterations + 1
            elseif sig.flattenVmBridge and Passes.unwrapFlattenVmBridge(ast) then
                recordPass("UnwrapFlattenVmBridge")
                settledResynthesis = false
                iterations = iterations + 1
            elseif scan.vm and scan.vm.ready and VmDecompiler.decompile(ast, targetVer) then
                recordPass("LiftVmBytecode")
                if Passes.removeAntiTamper(ast) then
                    recordPass("RemoveAntiTamper")
                end
                settledResynthesis = false
                iterations = iterations + 1
            elseif Passes.unsplitStrings(ast) then
                recordPass("UnsplitStrings")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif Passes.unproxifyLocals(ast) then
                recordPass("UnproxifyLocals")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif Passes.resolveConstantArray(ast) then
                recordPass("ResolveConstantArray")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif Passes.decryptStrings(ast) then
                recordPass("DecryptStrings")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif Passes.removeAntiTamper(ast) then
                recordPass("RemoveAntiTamper")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif Passes.removeWatermarks(ast) then
                recordPass("RemoveWatermarks")
                maybeSimplifyCells()
                settledResynthesis = false
                iterations = iterations + 1
            elseif CffDecompiler.unflatten(ast, targetVer) then
                recordPass("UnflattenControlFlow")
                finishUnflatten()
                settledResynthesis = false
                iterations = iterations + 1
            elseif Passes.unwrapFlattenVmBridge(ast) then
                recordPass("UnwrapFlattenVmBridge")
                settledResynthesis = false
                iterations = iterations + 1
            elseif VmDecompiler.decompile(ast, targetVer) then
                recordPass("LiftVmBytecode")
                if Passes.removeAntiTamper(ast) then
                    recordPass("RemoveAntiTamper")
                end
                settledResynthesis = false
                iterations = iterations + 1
            elseif sig.addedVarargs and Passes.removeAddedVarargs(ast) then
                recordPass("RemoveAddedVarargs")
                settledResynthesis = false
                iterations = iterations + 1
            elseif progressed then
                settledResynthesis = false
                iterations = iterations + 1
            elseif hadStructuralPasses and not settledResynthesis then
                settledResynthesis = true
                local unlocked = runResynthesis()
                if maybeSimplifyCells() then
                    unlocked = true
                    runResynthesis()
                end
                if Passes.unwrapFunction(ast) then
                    recordPass("UnwrapFunction")
                    unlocked = true
                end
                if Passes.removeAddedVarargs(ast) then
                    recordPass("RemoveAddedVarargs")
                    unlocked = true
                end
                if unlocked then
                    iterations = iterations + 1
                else
                    break
                end
            else
                break
            end
        end

        if hadStructuralPasses and not settledResynthesis then
            runResynthesis()
            if Passes.removeAddedVarargs(ast) then
                recordPass("RemoveAddedVarargs")
            end
        end

        if self.normalizeIdentifiers then
            local renamed = normalizeIdentifiers(ast, targetVer, hadStructuralPasses)
            if renamed then
                recordPass("NormalizeIdentifiers")
            end
        end
    end)

    Logger.logLevel = savedLevel
    if not okRun then
        error(tostring(runErr), 0)
    end

    return {
        luaVersion = targetVer,
        detected = initialDetection,
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

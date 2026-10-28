local logger = require("logger")

local IDENT_PREFIX = "__prometheus_"
local Scope = {}

local scopeI = 0
local function nextName()
    scopeI = scopeI + 1
    return "local_scope_" .. tostring(scopeI)
end

local function generateWarning(token, message)
    return "Warning at Position " .. tostring(token.line) .. ":" .. tostring(token.linePos) .. ", " .. message
end

function Scope:new(parentScope, name)
    local scope = {
        isGlobal = false,
        parentScope = parentScope,
        variables = {},
        referenceCounts = {},
        variablesLookup = {},
        variablesFromHigherScopes = {},
        skipIdLookup = {},
        name = name or nextName(),
        children = {},
        level = parentScope.level and (parentScope.level + 1) or 1,
    }
    setmetatable(scope, self)
    self.__index = self
    parentScope:addChild(scope)
    return scope
end

function Scope:newGlobal()
    local scope = {
        isGlobal = true,
        parentScope = nil,
        variables = {},
        variablesLookup = {},
        referenceCounts = {},
        skipIdLookup = {},
        name = "global_scope",
        children = {},
        level = 0,
    }
    setmetatable(scope, self)
    self.__index = self
    return scope
end

function Scope:getParent()
    return self.parentScope
end

function Scope:setParent(parentScope)
    self.parentScope:removeChild(self)
    parentScope:addChild(self)
    self.parentScope = parentScope
    self.level = parentScope.level + 1
end

local next_name_i = 1
function Scope:addVariable(name, token)
    if not name then
        name = string.format("%s%i", IDENT_PREFIX, next_name_i)
        next_name_i = next_name_i + 1
    end
    if self.variablesLookup[name] ~= nil then
        if token then
            logger:warn(generateWarning(token, "the variable \"" .. name .. "\" is already defined in that scope"))
        else
            logger:error(string.format("A variable with the name \"%s\" was already defined", name))
        end
    end
    table.insert(self.variables, name)
    local id = #self.variables
    self.variablesLookup[name] = id
    return id
end

function Scope:enableVariable(id)
    local name = self.variables[id]
    self.variablesLookup[name] = id
end

function Scope:addDisabledVariable(name, token)
    if not name then
        name = string.format("%s%i", IDENT_PREFIX, next_name_i)
        next_name_i = next_name_i + 1
    end
    if self.variablesLookup[name] ~= nil then
        if token then
            logger:warn(generateWarning(token, "the variable \"" .. name .. "\" is already defined in that scope"))
        else
            logger:warn(string.format("a variable with the name \"%s\" was already defined", name))
        end
    end
    table.insert(self.variables, name)
    return #self.variables
end

function Scope:addIfNotExists(id)
    if not self.variables[id] then
        local name = string.format("%s%i", IDENT_PREFIX, next_name_i)
        next_name_i = next_name_i + 1
        self.variables[id] = name
        self.variablesLookup[name] = id
    end
    return id
end

function Scope:hasVariable(name)
    if self.isGlobal then
        if self.variablesLookup[name] == nil then
            self:addVariable(name)
        end
        return true
    end
    return self.variablesLookup[name] ~= nil
end

function Scope:getVariables()
    return self.variables
end

function Scope:resetReferences(id)
    self.referenceCounts[id] = 0
end

function Scope:getReferences(id)
    return self.referenceCounts[id] or 0
end

function Scope:removeReference(id)
    self.referenceCounts[id] = (self.referenceCounts[id] or 0) - 1
end

function Scope:addReference(id)
    self.referenceCounts[id] = (self.referenceCounts[id] or 0) + 1
end

function Scope:resolve(name)
    if self:hasVariable(name) then
        return self, self.variablesLookup[name]
    end
    assert(self.parentScope, "No Global Variable Scope was Created!")
    local scope, id = self.parentScope:resolve(name)
    self:addReferenceToHigherScope(scope, id, nil, true)
    return scope, id
end

function Scope:resolveGlobal(name)
    if self.isGlobal and self:hasVariable(name) then
        return self, self.variablesLookup[name]
    end
    assert(self.parentScope, "No Global Variable Scope was Created!")
    local scope, id = self.parentScope:resolveGlobal(name)
    self:addReferenceToHigherScope(scope, id, nil, true)
    return scope, id
end

function Scope:getVariableName(id)
    return self.variables[id]
end

function Scope:removeVariable(id)
    local name = self.variables[id]
    self.variables[id] = nil
    self.variablesLookup[name] = nil
    self.skipIdLookup[id] = true
end

function Scope:addChild(scope)
    for higherScope, ids in pairs(scope.variablesFromHigherScopes) do
        for id, count in pairs(ids) do
            if count and count > 0 then
                self:addReferenceToHigherScope(higherScope, id, count)
            end
        end
    end
    table.insert(self.children, scope)
end

function Scope:clearReferences()
    self.referenceCounts = {}
    self.variablesFromHigherScopes = {}
end

function Scope:removeChild(child)
    for i, v in ipairs(self.children) do
        if v == child then
            for higherScope, ids in pairs(v.variablesFromHigherScopes) do
                for id, count in pairs(ids) do
                    if count and count > 0 then
                        self:removeReferenceToHigherScope(higherScope, id, count)
                    end
                end
            end
            return table.remove(self.children, i)
        end
    end
end

function Scope:getMaxId()
    return #self.variables
end

function Scope:addReferenceToHigherScope(scope, id, n, b)
    n = n or 1
    if self.isGlobal then
        if not scope.isGlobal then
            logger:error(string.format("Could not resolve Scope \"%s\"", scope.name))
        end
        return
    end
    if scope == self then
        self.referenceCounts[id] = (self.referenceCounts[id] or 0) + n
        return
    end
    if not self.variablesFromHigherScopes[scope] then
        self.variablesFromHigherScopes[scope] = {}
    end
    local scopeReferences = self.variablesFromHigherScopes[scope]
    if scopeReferences[id] then
        scopeReferences[id] = scopeReferences[id] + n
    else
        scopeReferences[id] = n
    end
    if not b then
        self.parentScope:addReferenceToHigherScope(scope, id, n)
    end
end

function Scope:removeReferenceToHigherScope(scope, id, n, b)
    n = n or 1
    if self.isGlobal then
        return
    end
    if scope == self then
        self.referenceCounts[id] = (self.referenceCounts[id] or 0) - n
        return
    end
    if not self.variablesFromHigherScopes[scope] then
        self.variablesFromHigherScopes[scope] = {}
    end
    local scopeReferences = self.variablesFromHigherScopes[scope]
    if scopeReferences[id] then
        scopeReferences[id] = scopeReferences[id] - n
    else
        scopeReferences[id] = 0
    end
    if not b then
        self.parentScope:removeReferenceToHigherScope(scope, id, n)
    end
end

return Scope

local logger = {}

logger.LogLevel = {
    Error = 0,
    Warn = 1,
    Log = 2,
    Info = 2,
    Debug = 3,
}

logger.logLevel = logger.LogLevel.Warn

logger.debugCallback = function(msg)
    io.stderr:write("[DEBUG] " .. tostring(msg) .. "\n")
end

function logger:debug(...)
    if self.logLevel >= self.LogLevel.Debug then
        self.debugCallback(...)
    end
end

logger.logCallback = function(msg)
    io.stderr:write("[INFO] " .. tostring(msg) .. "\n")
end

function logger:log(...)
    if self.logLevel >= self.LogLevel.Log then
        self.logCallback(...)
    end
end

function logger:info(...)
    if self.logLevel >= self.LogLevel.Log then
        self.logCallback(...)
    end
end

logger.warnCallback = function(msg)
    io.stderr:write("[WARN] " .. tostring(msg) .. "\n")
end

function logger:warn(...)
    if self.logLevel >= self.LogLevel.Warn then
        self.warnCallback(...)
    end
end

logger.errorCallback = function(msg)
    error(tostring(msg), 2)
end

function logger:error(...)
    self.errorCallback(...)
    error("Logger errorCallback returned without raising an error")
end

return logger

class ConfigurationError(Exception):
    """
    Error which is meant to be raised when a configuration entry is invalid.
    """
    def __init__(self, message):
        self.message = message

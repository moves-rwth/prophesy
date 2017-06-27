class ModuleError(Exception):
    """
    Error which is meant to be raised when importing a module is not possible.
    """
    def __init__(self, message):
        self.message = message


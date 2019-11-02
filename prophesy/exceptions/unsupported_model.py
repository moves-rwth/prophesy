class UnsupportedModel(Exception):
    """
    Error which is meant to be raised when the model at hand is not supported by a solver.
    """

    def __init__(self, message):
        """
        Constructor.
        :param message: Error message.
        """
        self.message = message

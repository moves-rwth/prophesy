class NotEnoughInformationError(Exception):
    """
    Error which is meant to be raised when the solver does not have sufficient information to execute the request.
    """

    def __init__(self, message):
        """
        Constructor.
        :param message: Error message.
        """
        self.message = message

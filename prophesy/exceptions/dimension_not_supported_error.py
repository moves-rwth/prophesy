class DimensionNotSupportedError(Exception):
    """
    Error which is meant to be raised when the dimension of the problem is not supported.
    """

    def __init__(self, message, min_supported_dim, max_supported_dim, requested_dim):
        """
        Constructor.
        :param message: Error message.
        :param min_supported_dim: Minimal number of supported dimensions.
        :param max_supported_dim: Maximal number of supported dimensions.
        :param requested_dim: Requested number of dimensions.
        """
        self.message = message
        self.min_supported_dim = min_supported_dim
        self.max_supported_dim = max_supported_dim
        self.requested_dim = requested_dim

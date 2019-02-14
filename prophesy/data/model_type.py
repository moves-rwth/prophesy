from enum import Enum


class ModelType(Enum):
    """
    The type of a Markovian model.
    """
    DTMC = 0
    MDP = 1
    CTMC = 2
    MA = 3

    def is_continuous_time(self):
        """
        Checks whether the model type is continuous-time
        :param model_type: 
        :return: 
        """
        return self in [ModelType.CTMC, ModelType.MA]


def model_is_nondeterministic(model_type):
    """
    Checks whether the model type is non-deterministic.
    :param model_type: 
    :return: True, if the model type encodes a model with potential non-determinism.
    """
    assert isinstance(model_type, ModelType)
    return model_type in [ModelType.MDP, ModelType.MA]

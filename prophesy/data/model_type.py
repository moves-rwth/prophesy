from enum import Enum

class ModelType(Enum):
    DTMC = 0
    MDP = 1
    CTMC = 2
    MA = 3

def model_is_nondeterministic(model_type):
    return model_type in [ModelType.MDP, ModelType.MA]
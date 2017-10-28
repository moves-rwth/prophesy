import random

import numpy as np


def set_random_seeds(py_seed=42, np_seed=23):
    random.seed(py_seed)
    np.random.seed(np_seed)

import numpy as np

from itertools import product

class IterableParam:
    def __init__(self, param, steps, max_value=1, bound_distance=0.2):
        self.paramvalues = np.array([0]*len(param),dtype='f')
        self.iter_params = np.array(range(0,len(param)))
        self.param = param
        self.length = len(param)
        self.steps = steps
        self.bound_distance = bound_distance
        self.max_value = max_value

    def __iter__(self):
        for x in product(range(0,self.steps), repeat=len(self.param)):
            self.paramvalues[self.iter_params] = np.array(x)*((1-self.bound_distance*2)/(self.steps-1))*self.max_value + [self.bound_distance] * len(self.param)
            yield list(zip(self.param,self.paramvalues.tolist()))
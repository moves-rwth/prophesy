from sampling.sampling import Sampler
from sympy.core.numbers import Rational
from collections import OrderedDict

class RatFuncSampling(Sampler):
    """Sample based on sympy rational function"""
    def __init__(self, ratfunc, parameters, rational=False):
        super().__init__()

        self.parameters = parameters
        self.ratfunc = ratfunc
        self.rational = rational

    def perform_sampling(self, samplepoints):
        samples = {}
        for pt in samplepoints:
            if self.rational:
                samples[pt] = self.ratfunc.eval({x:Rational(y) for x,y in zip(self.parameters, pt)}).evalf()
            else:
                samples[pt] = self.ratfunc.eval({x:y for x,y in zip(self.parameters, pt)}).evalf()
        return OrderedDict(samples.items())

from collections import OrderedDict
from sampling.sampling import Sampler
from sympy.core.numbers import Rational
from sympy.core.sympify import sympify
from sympy.polys import Poly

from libpycarl import Parser
import libpycarl

from pprint import pprint


class CarlSampling(Sampler):
    """Sample based on CARL library"""
    def __init__(self, ratfunc, parameters):
        super().__init__()

        self.parameters = parameters
        self.ratfunc = ratfunc

        parser = Parser()
        self.poly_vars = [libpycarl.VariablePool.getFreshVariable(str(p), libpycarl.VariableType.REAL) for p in self.parameters]
        for v in self.poly_vars:
            parser.addVariable(v)
        self.poly = parser.rationalFunction(str(self.ratfunc))

    def perform_sampling(self, samplepoints):
        samples = {}
        for pt in samplepoints:
            evaldict = {x: libpycarl.Rational(y) for x, y in zip(self.poly_vars, pt)}
            value = float((self.poly.evaluate(evaldict)))
            samples[pt] = value
        return OrderedDict(samples.items())

from sampling.sampling import Sampler
from sympy.core.numbers import Rational
from collections import OrderedDict
from sympy.polys import Poly
from sympy.core.sympify import sympify

from libpycarl import parsePolynomial, parseRationalFunction, RationalFunction
import libpycarl

from pprint import pprint

class CarlSampling(Sampler):
    """Sample based on sympy rational function"""
    def __init__(self, ratfunc, parameters, rational=False):
        super().__init__()

        self.parameters = parameters
        self.ratfunc = ratfunc
        self.rational = rational

        self.poly = parseRationalFunction(str(self.ratfunc))

        vars = self.poly.gatherVariables()
        self.poly_vars = []
        for p in self.parameters:
            for v in vars:
                if str(v) == str(p):
                    self.poly_vars.append(v)
                    break
            else:
                assert False, "Cannot match variable to parameter"

    def perform_sampling(self, samplepoints):
        samples = {}
        for pt in samplepoints:
            evaldict = {x:libpycarl.Rational(y) for x,y in zip(self.poly_vars, pt)}
            value = float((self.poly.evaluate(evaldict)))
            samples[pt] = value
        return OrderedDict(samples.items())

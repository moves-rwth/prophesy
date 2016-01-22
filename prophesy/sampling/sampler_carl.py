from collections import OrderedDict
from sampling.sampling import Sampler
from sympy.core.numbers import Rational
from sympy.core.sympify import sympify
from sympy.polys import Poly
from config import configuration

class CarlSampling(Sampler):
    """Sample based on CARL library"""
    def __init__(self, ratfunc, parameters):
        super().__init__()

        if not configuration.is_module_available("pycarl"):
            raise ModuleError("Module pycarl is needed for sampling with CARL")

        from pycarl.core import Parser
        import pycarl

        self.parameters = parameters
        self.ratfunc = ratfunc

        parser = Parser()
        self.poly_vars = [pycarl.core.VariablePool.getFreshVariable(str(p), pycarl.core.VariableType.REAL) for p in self.parameters]
        for v in self.poly_vars:
            parser.addVariable(v)

        ratfuncstr = str(self.ratfunc).replace("**", "^")
        print(ratfuncstr)
        self.poly = parser.rationalFunction(ratfuncstr)
        print(str(self.poly))

    def perform_sampling(self, samplepoints):
        samples = {}
        for pt in samplepoints:
            evaldict = {x:pycarl.core.Rational(y) for x,y in zip(self.poly_vars, pt)}
            value = float((self.poly.evaluate(evaldict)))
            samples[pt] = value
        return OrderedDict(samples.items())


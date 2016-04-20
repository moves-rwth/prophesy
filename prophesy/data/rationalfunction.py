from pycarl import Rational, Polynomial, RationalFunction as RatFun

#TODO: Technically this class is obsolete (carl can store RF directly), but
# it makes checking for consistency easier
class RationalFunction:
    """Represents rational function, consisting of
    a Poly nominator and Poly denominator"""

    def __init__(self, rational_func):
        """
        @param rational_func pycarl.RationalFunction
        """
        if not isinstance(rational_func, RatFun):
            # Cast Polynomial or lower class
            rational_func = RatFun(Polynomial(rational_func), Polynomial(Rational(1)))
        self.rational_func = rational_func
        self.nominator = rational_func.numerator
        self.denominator = rational_func.denominator
        # Set of variables found in function, used for validation during eval
        self._variables = self.rational_func.gather_variables()

    def eval(self, evaluation):
        """
        @param: evaluation SamplePoint
        @return pycarl.Rational
        """
        #TODO: pycarl does not compare Variable correctly, hash fail?
        #assert set(evaluation.keys()) == self._variables, "Evaluating a wrong bunch of variables"
        return self.rational_func.evaluate(evaluation)

    def __str__(self):
        return str(self.rational_func)

    def __repr__(self):
        return "RationalFunction({!r})".format(self.rational_func)

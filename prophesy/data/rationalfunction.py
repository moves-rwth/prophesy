from pycarl import RationalFunction

#TODO: Technically this class is obsolete (carl can store RF directly), but
# it makes checking for consistency easier
class RationalFunction:
    """Represents rational function, consisting of
    a Poly nominator and Poly denominator"""

    def __init__(self, rational_func):
        """
        @param rational_func pycarl.RationalFunction
        """
        if not isinstance(rational_func, RationalFunction):
            # Cast Polynomial or lower class
            rational_func = RationalFunction(rational_func)
        self.rational_func = rational_func
        self.nominator = rational_func.numerator
        self.denominator = rational_func.denominator
        # Set of variables found in function
        self.variables = self.rational_func.gather_variables()

    def eval(self, evaluation):
        """
        @param: evaluation SamplePoint
        @return pycarl.Rational
        """
        assert set(evaluation.keys()) == self.variables, "Evaluating a wrong bunch of variables"
        return self.rational_func.evaluate(evaluation)

    def __str__(self):
        return str(self.rational_func)

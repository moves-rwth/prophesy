class RationalFunction:
    """Represents rational function, consisting of
    a Poly nominator and Poly denominator"""
    evaluation_precision = 10
    def __init__(self, nominator, denominator):
        self.nominator = nominator
        self.denominator = denominator

    def evalf(self, *args, **kwargs):
        return (self.nominator / self.denominator).evalf(RationalFunction.evaluation_precision)

    def subs(self, *args, **kwargs):
        newNom = self.nominator.subs(*args, **kwargs)
        newDen = self.denominator.subs(*args, **kwargs)
        return RationalFunction(newNom, newDen)

    def __str__(self):
        return "(" + str(self.nominator)[5:].split(",")[0] + ") / (" + str(self.denominator)[5:].split(",")[0] + ")"

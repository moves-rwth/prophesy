class RationalFunction:
    """Represents rational function, consisting of
    a Poly nominator and Poly denominator"""
    evaluation_precision = 10
    def __init__(self, nominator, denominator):
        self.nominator = nominator
        self.denominator = denominator

    def eval(self, x, a=None, auto=True):
        eval_nom = self.nominator.eval(x, a, auto)
        eval_den = self.denominator.eval(x, a, auto)
        return eval_nom/eval_den

    def evalf(self, *args, **kwargs):
        return (self.nominator / self.denominator).evalf(RationalFunction.evaluation_precision)

    def subs(self, *args, **kwargs):
        newNom = self.nominator.subs(*args, **kwargs)
        newDen = self.denominator.subs(*args, **kwargs)
        return RationalFunction(newNom, newDen)

    def __str__(self):
        return "({}) / ({})".format(self.nominator.as_expr(), self.denominator.as_expr())

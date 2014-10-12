from data.pretty_polynomial import *
from sympy import sstr

class RationalFunction:
    evaluation_precision = 10
    def __init__(self, nominator, denominator):
        self.nominator = nominator
        self.denominator = denominator
        
    def evaluate(self, evaluation):
        evaluationNom = self.nominator
        evaluationDen = self.denominator
        for [variable, value] in evaluation:
            evaluationNom = evaluationNom.subs(variable, value)
            evaluationDen = evaluationDen.subs(variable, value)
        evalVal = (evaluationNom/evaluationDen).evalf(RationalFunction.evaluation_precision)
        return evalVal
    
    def __str__(self):
        return "(" + sstr(self.nominator) + "/" + sstr(self.denominator) + ")"
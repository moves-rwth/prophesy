from regions.region_checker import RegionChecker

class SmtRegionChecker(RegionChecker):
    def __init__(self, smt2interface):
        self._smt2interface = smt2interface

    def check(self):
        pass
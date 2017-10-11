from prophesy.util import check_filepath_for_reading
from prophesy.data.property import Property

class PctlFile:
    """
    Wrapper for pctl files, which contain a list of pctl formulae
    """
    def __init__(self, location):
        check_filepath_for_reading(location)
        self.location = location
        self.formulas = []
        self._parse()

    def _parse(self):
        with open(self.location, 'r') as f:
            for line in f:
                if line.startswith('#') or line.startswith("//") or line.strip() == "":
                    pass
                else:

                    self.formulas.append(Property.from_string(line.strip()))

    def get(self, index):
        if index >= self.get_nr_formulas():
            raise IndexError("The PCTL file only contains {0} formulas, index {1} is too large".format(self.get_nr_formulas(), index))
        return self.formulas[index]

    def get_nr_formulas(self):
        return len(self.formulas)

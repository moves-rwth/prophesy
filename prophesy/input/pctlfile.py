class PctlFile:
    def __init__(self, location):
        self.location = location
        self.formulas = []

    def parse(self):
        with open(self.location, 'r') as f:
            for line in f:
                if line.startswith('#') or line.strip() == "":
                    pass
                else:
                    self.formulas.append(line.strip)

    def get(self, index):
        return self.formulas[index]

    def get_nr_formulas(self):
        return len(self.formulas)
def parse_pctl_file(path):
    pctl_formulas = []
    # open the file
    with open(path, 'r') as f:
        for line in f:
            comment_stripped = line.split("#")[0].rstrip();
            if comment_stripped != "":
                #TODO use pctl_formula object
                pctl_formulas.append(comment_stripped)
    return pctl_formulas
import os, sys

"""
    This file encodes Einstein's puzzle in cnf form.
"""


def create_map(house_attributes, man_attributes):
    notation_map = {}
    variable_map = {}
    variable_index = 1
    # House attributes
    for h_attr in house_attributes:
        for value in h_attr:
            for i in HOUSE_INDICES:
                notation_map[H(i, value)] = variable_index
                variable_map[variable_index] = H(i, value)
                variable_index += 1
    # Man attributes
    for m_attr in man_attributes:
        for value in m_attr:
            for i in HOUSE_INDICES:
                notation_map[M(i, value)] = variable_index
                variable_map[variable_index] = M(i, value)
                variable_index += 1
    return notation_map, variable_map


# notation for house attributes
def H(i, house_attr):
    return 'H(' + str(i) + ',' + house_attr + ')'


def M(i, man_attr):
    return 'M(' + str(i) + ',' + man_attr + ')'


def get_notation_from(variable_index):
    return VARIABLE_MAP[variable_index]


def create_einstein_puzzle():
    clauses = []
    # Problem encoding
    # C1: Each house has a different color
    clauses += different_house_attr(HOUSE_COLOR)
    # C2: Each house must only have one color
    clauses += exactly_one_house_attr(HOUSE_COLOR)
    # C3: Each house lives a man with different nationality
    clauses += different_house_attr(NATIONALITIES)
    # C4: Each house lives a man with only one nationality
    clauses += exactly_one_house_attr(NATIONALITIES)
    # C5: Each man drinks a different beverage
    clauses += different_man_attr(BEVERAGES)
    # C6: Each man drink only one beverage
    clauses += exactly_one_man_attr(BEVERAGES)
    # C7: Each man smokes a different cigarette
    clauses += different_man_attr(CIGARS)
    # C8: Each man smokes only one cigarrete
    clauses += exactly_one_man_attr(CIGARS)
    # C9: Each man keeps a different pet
    clauses += different_man_attr(PETS)
    # C10: Each man keeps only one pet
    clauses += exactly_one_man_attr(PETS)
    # Hint representations:
    # H1: The Brit lives in the red house.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[H(i, 'red')]) + ' ' + str(NOTATION_MAP[H(i, 'Brit')]))
    # H2: The Swede keeps dogs as pets.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[H(i, 'Swede')]) + ' ' + str(NOTATION_MAP[M(i, 'dogs')]))
    # H3: The Dane drinks tea.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[H(i, 'Dane')]) + ' ' + str(NOTATION_MAP[M(i, 'tea')]))
    # H4: The green house is on the left of the white house.
    for j in [1, 2, 3, 4]:
        clauses.append(str(- NOTATION_MAP[H(j, 'green')]) + ' ' + str(NOTATION_MAP[H(j + 1, 'white')]))
    # H5: The green house's owner drinks coffee.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[H(i, 'green')]) + ' ' + str(NOTATION_MAP[M(i, 'coffee')]))
    # H6: The person who smokes Pall Mall rears birds.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[M(i, 'PallMall')]) + ' ' + str(NOTATION_MAP[M(i, 'birds')]))
    # H7: The owner of the yellow house smokes Dunhill.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[H(i, 'yellow')]) + ' ' + str(NOTATION_MAP[M(i, 'Dunhill')]))
    # H8: The man living in the center house drinks milk.
    clauses.append(str(NOTATION_MAP[M(3, 'milk')]))
    # H9: The Norwegian lives in the first house.
    clauses.append(str(NOTATION_MAP[H(1, 'Norwegian')]))
    # H10: The man who smokes Blends lives next to the one who keeps cats
    clauses.append(str(- NOTATION_MAP[M(1, 'Blends')]) + ' ' + str(NOTATION_MAP[M(2, 'cats')]))
    for j in [2, 3, 4]:
        clauses.append(str(- NOTATION_MAP[M(j, 'Blends')]) + ' ' +
                       str(NOTATION_MAP[M(j - 1, 'cats')]) + ' ' + str(NOTATION_MAP[M(j + 1, 'cats')]))
    clauses.append(str(- NOTATION_MAP[M(5, 'Blends')]) + ' ' + str(NOTATION_MAP[M(4, 'cats')]))
    # H11: The man who keeps the horse lives next to the man who smokes Dunhill
    clauses.append(str(- NOTATION_MAP[M(1, 'horses')]) + ' ' + str(NOTATION_MAP[M(2, 'Dunhill')]))
    for j in [2, 3, 4]:
        clauses.append(str(- NOTATION_MAP[M(j, 'horses')]) + ' ' +
                       str(NOTATION_MAP[M(j - 1, 'Dunhill')]) + ' ' + str(NOTATION_MAP[M(j + 1, 'Dunhill')]))
    clauses.append(str(- NOTATION_MAP[M(5, 'horses')]) + ' ' + str(NOTATION_MAP[M(4, 'Dunhill')]))
    # H12: The owner who smokes Bluemasters drinks beer.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[M(i, 'Bluemasters')]) + ' ' + str(NOTATION_MAP[M(i, 'beer')]))
    # H13: The German smokes Prince.
    for i in HOUSE_INDICES:
        clauses.append(str(- NOTATION_MAP[H(i, 'German')]) + ' ' + str(NOTATION_MAP[M(i, 'Prince')]))
    # H14: The Norwegian lives next to the blue house.
    clauses.append(str(- NOTATION_MAP[H(1, 'Norwegian')]) + ' ' + str(NOTATION_MAP[H(2, 'blue')]))
    for j in [2, 3, 4]:
        clauses.append(str(- NOTATION_MAP[H(j, 'Norwegian')]) + ' ' +
                       str(NOTATION_MAP[H(j - 1, 'blue')]) + ' ' + str(NOTATION_MAP[H(j + 1, 'blue')]))
    clauses.append(str(- NOTATION_MAP[H(5, 'Norwegian')]) + ' ' + str(NOTATION_MAP[H(4, 'blue')]))
    # H15: The man who smokes Blends has a neighbor who drinks water.
    clauses.append(str(- NOTATION_MAP[M(1, 'Blends')]) + ' ' + str(NOTATION_MAP[M(2, 'water')]))
    for j in [2, 3, 4]:
        clauses.append(str(- NOTATION_MAP[M(j, 'Blends')]) + ' ' +
                       str(NOTATION_MAP[M(j - 1, 'water')]) + ' ' + str(NOTATION_MAP[M(j + 1, 'water')]))
    clauses.append(str(- NOTATION_MAP[M(5, 'Blends')]) + ' ' + str(NOTATION_MAP[M(4, 'water')]))
    return clauses


# Encodes that house attribute attr must be different for every house indices
def different_house_attr(h_attr):
    res = []
    for i in HOUSE_INDICES:
        excluded = HOUSE_INDICES.copy()
        excluded.remove(i)
        for i_prime in excluded:
            for attr in h_attr:
                res.append(str(- NOTATION_MAP[H(i, attr)]) + ' ' + str(- NOTATION_MAP[H(i_prime, attr)]))
    return res


# Encodes that man attribute attr must be different for every house indices
def different_man_attr(m_attr):
    res = []
    for i in HOUSE_INDICES:
        excluded = HOUSE_INDICES.copy()
        excluded.remove(i)
        for i_prime in excluded:
            for attr in m_attr:
                res.append(str(- NOTATION_MAP[M(i, attr)]) + ' ' + str(- NOTATION_MAP[M(i_prime, attr)]))
    return res


# Encodes that house attribute attr must exist exactly once for every house indices
def exactly_one_house_attr(h_attr):
    res = []
    for i in HOUSE_INDICES:
        for attr in h_attr:
            excluded = h_attr.copy()
            excluded.remove(attr)
            for attr_prime in excluded:
                res.append(str(- NOTATION_MAP[H(i, attr)]) + ' ' + str(- NOTATION_MAP[H(i, attr_prime)]))
    for i in HOUSE_INDICES:
        var_list = [str(NOTATION_MAP[H(i, attr)]) for attr in h_attr]
        res.append(' '.join(var_list))
    return res


# Encodes that man attribute attr must exist exactly once for every house indices
def exactly_one_man_attr(m_attr):
    res = []
    for i in HOUSE_INDICES:
        for attr in m_attr:
            excluded = m_attr.copy()
            excluded.remove(attr)
            for attr_prime in excluded:
                res.append(str(- NOTATION_MAP[M(i, attr)]) + ' ' + str(- NOTATION_MAP[M(i, attr_prime)]))
    for i in HOUSE_INDICES:
        var_list = [str(NOTATION_MAP[M(i, attr)]) for attr in m_attr]
        res.append(' '.join(var_list))
    return res


# Attributes in the puzzle
HOUSE_INDICES = [1, 2, 3, 4, 5]
HOUSE_COLOR = ["red", "green", "yellow", "blue", "white"]
NATIONALITIES = ["Brit", "Swede", "Dane", "Norwegian", "German"]
HOUSE_ATTRIBUTES = [HOUSE_COLOR, NATIONALITIES]
BEVERAGES = ["tea", "coffee", "milk", "beer", "water"]
CIGARS = ["PallMall", "Dunhill", "Blends", "Bluemasters", "Prince"]
PETS = ["dogs", "birds", "cats", "horses", "fishes"]
MAN_ATTRIBUTES = [BEVERAGES, CIGARS, PETS]

# Notation map stores a map from notation H_(i, house_attribute) or M_(i, man_attribute) to variable index.
# Variable map stores a map from variable index to notation H_(i, house_attribute) or M_(i, man_attribute)
NOTATION_MAP, VARIABLE_MAP = create_map(HOUSE_ATTRIBUTES, MAN_ATTRIBUTES)

clauses = create_einstein_puzzle()
n_var = len(NOTATION_MAP)
n_clause = len(clauses)
# Print to dimacs format
print("c Einstein puzzle encoding in cnf")
print("c for CS4244 project 1")
print("p cnf {} {}".format(n_var, n_clause))
for c in clauses:
    print(c, end=' 0\n')

'''# Print the variables noteworthy to keep track of
# The house index of the man who keeps fish
print("House indices of man who keeps fish: {}".format([NOTATION_MAP[M(i, 'fishes')] for i in HOUSE_INDICES]))
# 4th house - x_124 is set true
print("Nationality of the fourth house is :{}".format([NOTATION_MAP[H(4, nation)] for nation in NATIONALITIES]))
# German - x_49 is set true'''


def show_assignment(assignment):
    for literal_index, value in assignment.items():
        if value:
            print("{} is set true".format(VARIABLE_MAP[literal_index]))

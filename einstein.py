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
    # Problem encoding
    # C1: Each house has a different color
    different_house_attr(HOUSE_COLOR)
    # C2: Each house must only have one color
    exactly_one_house_attr(HOUSE_COLOR)
    # C3: Each house lives a man with different nationality
    different_house_attr(NATIONALITIES)
    # C4: Each house lives a man with only one nationality
    exactly_one_house_attr(NATIONALITIES)
    # C5: Each man drinks a different beverage
    different_man_attr(BEVERAGES)
    # C6: Each man drink only one beverage
    exactly_one_man_attr(BEVERAGES)
    # C7: Each man smokes a different cigarette
    different_man_attr(CIGARS)
    # C8: Each man smokes only one cigarrete
    exactly_one_man_attr(CIGARS)
    # C9: Each man keeps a different pet
    different_man_attr(PETS)
    # C10: Each man keeps only one pet
    exactly_one_man_attr(PETS)
    # Hint representations:
    # H1: The Brit lives in the red house.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[H(i, 'red')] + ' ' + NOTATION_MAP[H(i, 'Brit')]
    # H2: The Swede keeps dogs as pets.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[H(i, 'Swede')] + ' ' + NOTATION_MAP[M(i, 'dogs')]
    # H3: The Dane drinks tea.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[H(i, 'Dane')] + ' ' + NOTATION_MAP[M(i, 'tea')]
    # H4: The green house is on the left of the white house.
    for j in [1, 2, 3, 4]:
        clause = - NOTATION_MAP[H(j, 'green')] + ' ' + NOTATION_MAP[H(j + 1, 'white')]
    # H5: The green house's owner drinks coffee.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[H(i, 'green')] + ' ' + NOTATION_MAP[M(i, 'coffee')]
    # H6: The person who smokes Pall Mall rears birds.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[M(i, 'PallMall')] + ' ' + NOTATION_MAP[M(i, 'birds')]
    # H7: The owner of the yellow house smokes Dunhill.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[H(i, 'yellow')] + ' ' + NOTATION_MAP[M(i, 'Dunhill')]
    # H8: The man living in the center house drinks milk.
    clause = NOTATION_MAP[M(3, 'milk')]
    # H9: The Norwegian lives in the first house.
    clause = NOTATION_MAP[H(1, 'Norwegian')]
    # H10: The man who smokes Blends lives next to the one who keeps cats
    clause = - NOTATION_MAP[M(1, 'Blends')] + ' ' + NOTATION_MAP[M(2, 'cats')]
    for j in [2, 3, 4]:
        clause = - NOTATION_MAP[M(j, 'Blends')] + ' ' \
                 + NOTATION_MAP[M(j - 1, 'cats')] + ' ' + NOTATION_MAP[M(j + 1, 'cats')]
    clause = - NOTATION_MAP[M(5, 'Blends')] + ' ' + NOTATION_MAP[M(4, 'cats')]
    # H11: The man who keeps the horse lives next to the man who smokes Dunhill
    clause = - NOTATION_MAP[M(1, 'horses')] + ' ' + NOTATION_MAP[M(2, 'Dunhill')]
    for j in [2, 3, 4]:
        clause = - NOTATION_MAP[M(j, 'horses')] + ' ' \
                 + NOTATION_MAP[M(j - 1, 'Dunhill')] + ' ' + NOTATION_MAP[M(j + 1, 'Dunhill')]
    clause = - NOTATION_MAP[M(5, 'horses')] + NOTATION_MAP[M(4, 'Dunhill')]
    # H12: The owner who smokes Bluemasters drinks beer.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[M(i, 'Bluemasters')] + ' ' + NOTATION_MAP[M(i, 'beer')]
    # H13: The German smokes Prince.
    for i in HOUSE_INDICES:
        clause = - NOTATION_MAP[H(i, 'German')] + ' ' + NOTATION_MAP[M(i, 'Prince')]
    # H14: The Norwegian lives next to the blue house.
    clause = - NOTATION_MAP[H(1, 'Norwegian')] + ' ' + NOTATION_MAP[H(2, 'blue')]
    for j in [2, 3, 4]:
        clause = - NOTATION_MAP[H(j, 'Norwegian')] + ' ' \
                 + NOTATION_MAP[H(j - 1, 'blue')] + ' ' + NOTATION_MAP[H(j + 1, 'blue')]
    clause = - NOTATION_MAP[H(5, 'Norwegian')] + ' ' + NOTATION_MAP[H(4, 'blue')]
    # H15: The man who smokes Blends has a neighbor who drinks water.
    clause = - NOTATION_MAP[M(1, 'Blends')] + NOTATION_MAP[M(2, 'water')]
    for j in [2, 3, 4]:
        clause = - NOTATION_MAP[M(j, 'Blends')] + ' ' \
                 + NOTATION_MAP[M(j - 1, 'water')] + ' ' + NOTATION_MAP[M(j + 1, 'water')]
    clause = - NOTATION_MAP[M(5, 'Blends')] + NOTATION_MAP[M(4, 'water')]


# Encodes that house attribute attr must be different for every house indices
def different_house_attr(h_attr):
    for i in HOUSE_INDICES:
        excluded = HOUSE_INDICES.copy()
        excluded.remove(i)
        for i_prime in excluded:
            for attr in h_attr:
                clause = - NOTATION_MAP[H(i, attr)] + ' ' + - NOTATION_MAP[H(i_prime, attr)]


# Encodes that man attribute attr must be different for every house indices
def different_man_attr(m_attr):
    for i in HOUSE_INDICES:
        excluded = HOUSE_INDICES.copy()
        excluded.remove(i)
        for i_prime in excluded:
            for attr in m_attr:
                clause = - NOTATION_MAP[M(i, attr)] + ' ' + - NOTATION_MAP[M(i_prime, attr)]


# Encodes that house attribute attr must exist exactly once for every house indices
def exactly_one_house_attr(h_attr):
    for i in HOUSE_INDICES:
        for attr in h_attr:
            excluded = h_attr.copy()
            excluded.remove(attr)
            for attr_prime in excluded:
                clause = - NOTATION_MAP[H(i, attr)] + ' ' + - NOTATION_MAP[H(i, attr_prime)]
    for i in HOUSE_INDICES:
        var_list = [NOTATION_MAP[H(i, attr)] for attr in h_attr]
        clause = ' '.join(var_list)


# Encodes that man attribute attr must exist exactly once for every house indices
def exactly_one_man_attr(m_attr):
    for i in HOUSE_INDICES:
        for attr in m_attr:
            excluded = m_attr.copy()
            excluded.remove(attr)
            for attr_prime in excluded:
                clause = - NOTATION_MAP[M(i, attr)] + ' ' + - NOTATION_MAP[M(i, attr_prime)]
    for i in HOUSE_INDICES:
        var_list = [NOTATION_MAP[M(i, attr)] for attr in m_attr]
        clause = ' '.join(var_list)


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

if __name__ == "main":
    create_einstein_puzzle()

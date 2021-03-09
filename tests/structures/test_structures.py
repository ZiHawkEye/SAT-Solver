from notation import Literal, Clause, Formula


def test_equality():
    literal1 = Literal("-3")
    literal2 = Literal("-3")
    literal3 = Literal("3")
    clause1 = Clause({literal2, literal3})
    clause2 = Clause({literal1, literal2})
    clause3 = Clause({literal1, literal3})
    formula1 = Formula({clause1, clause3}, 3)
    formula2 = Formula({clause1, clause2}, 3)
    formula3 = Formula({clause2, clause3}, 3)
    assert literal1 == literal2
    assert literal3 != literal2
    assert clause1 == clause3
    assert clause1 != clause2
    assert len(clause2.literals) == 1
    assert formula1 != formula2
    assert formula2 == formula3


def test_set_insertion():
    c1 = Clause({Literal(12), Literal(33), Literal(-6)})
    c2 = Clause({Literal(12), Literal(33), Literal(-6)})
    c3 = Clause({Literal(12), Literal(33), Literal(-6)})
    c1.watched_literals = {Literal(-6), Literal(33)}
    d = {
        Literal(12): set([c1])
    }
    assert len(d[Literal(12)]) == 1
    assert c2 in d[Literal(12)]
    d[Literal(12)].remove(c2)
    assert len(d[Literal(12)]) == 0

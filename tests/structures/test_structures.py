from notation import Literal, Clause, Formula


def test_equality():
    literal1 = Literal("-3")
    literal2 = Literal("-3")
    literal3 = Literal("3")
    c1 = Clause({literal2, literal3})
    c2 = Clause({literal1, literal2})
    c3 = Clause({literal1, literal3})
    f1 = Formula({c1, c3})
    f2 = Formula({c1, c2})
    f3 = Formula({c2, c3})
    assert literal1 == literal2
    assert literal3 != literal2
    assert c1 == c3
    assert c1 != c2
    assert len(c2.literals) == 1
    assert f1 != f2
    assert f2 == f3
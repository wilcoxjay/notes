function method abs(x: int): int
{
    if x < 0 then - x else x
}

iterator AllInts() yields (x: int)
    yield ensures x !in xs[..|xs|-1]
    yield ensures forall y :: abs(y) < x ==> y in xs
    yield ensures x < 0 ==> -x in xs
{
    assert xs == [];
    x := 0;
    yield;
    while true
    {
        x := x + 1;
        yield;
        x := -x;
        yield;
        x := -x;
    }
}

method FindInt(n: int)
{
    var it := new AllInts();
    var more := it.MoveNext();
    assert more;
    if it.x == n {
        return;
    }

    while true
        invariant it.x <= 0
        invariant fresh(it._new)
        decreases n + it.x
        modifies it
    {
        more := it.MoveNext();
        assert more;
        if it.x == n {
            break;
        }

        more := it.MoveNext();
        assert more;
        if it.x == n {
            break;
        }
    }
}

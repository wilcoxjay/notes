class ArrayElementInitializer {
    predicate Valid(i: int, a: object)
        reads this
    method Init(i: int) returns (a: object)
        modifies this
        ensures Valid(i, a)
        ensures forall x, y :: old(allocated(y)) && old(Valid(x, y)) ==> Valid(x, y)
}

method InitializeArray(aei: ArrayElementInitializer, a: array<object>)
    requires aei != null && a != null
    modifies a, aei
    ensures forall x :: 0 <= x < a.Length ==> aei.Valid(x, a[x])
{
    var i := 0;
    while i < a.Length
        modifies a, aei
        invariant 0 <= i <= a.Length
        invariant forall x :: 0 <= x < i ==> aei.Valid(x, a[x])
    {
        a[i] := aei.Init(i);
        i := i + 1;
    }
}

////////////////////////////////////////////////////////////////////////////////

trait TraitArrayElementInitializer {
    predicate Valid(i: int, a: object)
        reads this
    method Init(i: int) returns (a: object)
        modifies this
        ensures Valid(i, a)
        ensures forall x, y :: old(allocated(y)) && old(Valid(x, y)) ==> Valid(x, y)
}

method TraitInitializeArray(aei: TraitArrayElementInitializer, a: array<object>)
    requires aei != null && a != null
    modifies a, aei
    ensures forall x :: 0 <= x < a.Length ==> aei.Valid(x, a[x])
{
    var i := 0;
    while i < a.Length
        modifies a, aei
        invariant 0 <= i <= a.Length
        invariant forall x :: 0 <= x < i ==> aei.Valid(x, a[x])
    {
        a[i] := aei.Init(i);
        i := i + 1;
    }
}


// RUN: /compile:0

method ArrayInit<A>(f: int -> A, a: array<A>)
    requires a != null
    requires forall x :: 0 <= x < a.Length ==> f.requires(x)
    requires forall x :: 0 <= x < a.Length ==> a !in f.reads(x)
    modifies a
    ensures forall x :: 0 <= x < a.Length ==> f.requires(x)
    ensures forall x :: 0 <= x < a.Length ==> a[x] == f(x)
{
    var i := 0;
    while i < a.Length
        modifies a
        invariant 0 <= i <= a.Length
        invariant forall x :: 0 <= x < i ==> a[x] == f(x)
    {
        a[i] := f(i);
        i := i + 1;
    }
}

type Elt = ()

trait ArrayElementInitializer {
    predicate Valid(i: int, a: Elt)
//        reads this
    method Init(i: int) returns (a: Elt)
        modifies this
        ensures Valid(i, a)
        ensures forall x, y :: old(allocated(y)) && old(Valid(x, y)) ==> Valid(x, y)
}

method InitializeArray(aei: ArrayElementInitializer, a: array<Elt>)
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
        assert forall x :: 0 <= x < i ==> aei.Valid(x, a[x]);
//        assert aei !in aei.Valid.reads;
        var ai := aei.Init(i);
        assert aei.Valid(i, ai);
        
        forall x | 0 <= x < i ensures aei.Valid(x, a[x])
        {
            assert aei.Valid(x, a[x]);
        }
        i := i + 1;
    }
}

method ArrayMap<A>(f: A -> A, a: array<A>)
    requires a != null
    requires forall x :: a !in f.reads(x)
    requires forall x :: f.requires(x)
    modifies a
    ensures forall x :: 0 <= x < a.Length ==> a[x] == f(old(a[x]))
{
    var i := 0;
    while i < a.Length
        modifies a
        invariant 0 <= i <= a.Length
        invariant forall x :: i <= x < a.Length ==> a[x] == old(a[x])
        invariant forall x :: 0 <= x < i ==> a[x] == f(old(a[x]))
    {
        
        a[i] := f(a[i]);
        i := i + 1;
    }
}

method ArrayMapWithIndex<A>(f: (int, A) -> A, a: array<A>)
    requires a != null
    requires forall x, y :: 0 <= x < a.Length ==> a !in f.reads(x, y)
    requires forall x, y :: 0 <= x < a.Length ==> f.requires(x, y)
    modifies a
    ensures forall x :: 0 <= x < a.Length ==> a[x] == f(x, old(a[x]))
{
    var i := 0;
    while i < a.Length
        modifies a
        invariant 0 <= i <= a.Length
        invariant forall x :: i <= x < a.Length ==> a[x] == old(a[x])
        invariant forall x :: 0 <= x < i ==> a[x] == f(x, old(a[x]))
    {
        a[i] := f(i, a[i]);
        i := i + 1;
    }
}


method ArgMax<A>(f: A -> int, a: array<A>) returns (i: int)
    requires a != null && a.Length > 0
    requires forall x :: 0 <= x < a.Length ==> f.requires(a[x])
    ensures 0 <= i < a.Length
    ensures forall x :: 0 <= x < a.Length ==> f.requires(a[x])
    ensures forall x :: 0 <= x < a.Length ==> f(a[x]) <= f(a[i])
{
    i := 0;
    var j := 1;
    while j < a.Length
        invariant 0 <= i < j <= a.Length
        invariant forall x :: 0 <= x < j ==> f(a[x]) <= f(a[i])
    {
        if f(a[j]) > f(a[i]) {
            i := j;
        }
        j := j + 1;
    }
}

function last<A>(l: seq<A>): A
    requires |l| != 0
{
    l[|l| - 1]
}

method Foo(o: object)
{
    assert forall x: seq<int> :: o !in last.reads(x);
}

function all_but_last<A>(l: seq<A>): seq<A>
    requires |l| != 0
{
    l[0..|l|-1]
}

function FoldLeft<A, B>(f: (A, B) -> B, b: B, l: seq<A>): B
    reads f.reads
    requires forall x, y :: f.requires(x, y)
{
    if l == [] then
        b
    else
        FoldLeft(f, f(l[0], b), l[1..])
}

function FoldRight<A, B>(f: (A, B) -> B, b: B, l: seq<A>): B
    reads f.reads
    requires forall x, y :: f.requires(x, y)
{
    if l == [] then
        b
    else
        f(l[0], FoldRight(f, b, l[1..]))
}

lemma FoldRight_Comm<A, B>(f: (A, B) -> B, a: A, b: B, l: seq<A>)
    requires forall x, y :: f.requires(x, y)
    requires forall a1, a2, b :: f(a1, f(a2, b)) == f(a2, f(a1, b))
    ensures f(a, FoldRight(f, b, l)) == FoldRight(f, f(a, b), l)
{}

lemma FoldLeftRightAgree<A, B>(f: (A, B) -> B, b: B, l: seq<A>)
    requires forall x, y :: f.requires(x, y)
    requires forall a1, a2, b :: f(a1, f(a2, b)) == f(a2, f(a1, b))
    ensures FoldLeft(f, b, l) == FoldRight(f, b, l)
{
    if l != [] {
        calc {
            FoldLeft(f, b, l);
            FoldLeft(f, f(l[0], b), l[1..]);
                { FoldLeftRightAgree(f, f(l[0], b), l[1..]); }
            FoldRight(f, f(l[0], b), l[1..]);
                { FoldRight_Comm(f, l[0], b, l[1..]); }
            FoldRight(f, b, l);
        }
    }
}

method ArrayFold<A, B>(f: (A, B) -> B, b0: B, a: array<A>) returns (b: B)
    requires a != null && a.Length > 0
    requires forall x, y :: f.requires(x, y)
    ensures forall x, y :: f.requires(x, y)
    ensures b == FoldLeft(f, b0, a[..])
{
    b := b0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant FoldLeft(f, b, a[i..]) == FoldLeft(f, b0, a[..])
    {
        b := f(a[i], b);
        i := i + 1;
    }
}



method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
    requires a != null && a.Length > 0
    requires forall x, y :: cmp.requires(x, y)
    requires forall x, y :: cmp(x, y) || cmp(y, x);
    requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z);

    ensures forall x, y :: cmp.requires(x, y)
    ensures forall x :: 0 <= x < a.Length ==> cmp(a[x], max)
{
    max := a[0];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: 0 <= x < i ==> cmp(a[x], max)
    {
        if !cmp(a[i], max) {
            max := a[i];
        }
        i := i + 1;
    }
}

method GenericSort<A>(cmp: (A, A) -> bool, a: array<A>)
    requires a != null && a.Length > 0
    requires forall x, y :: a !in cmp.reads(x, y)
    requires forall x, y :: cmp.requires(x, y)
    requires forall x, y :: cmp(x, y) || cmp(y, x);
    requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z);
    modifies a
    ensures forall x, y :: cmp.requires(x, y)
    ensures forall x, y :: 0 <= x < y < a.Length ==> cmp(a[x], a[y])
{
    var i := 0;
    while i < a.Length
        modifies a
        invariant 0 <= i <= a.Length
        invariant forall x, y :: a !in cmp.reads(x, y)
        invariant forall x, y :: cmp.requires(x, y)
        invariant forall x, y :: cmp(x, y) || cmp(y, x)
        invariant forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z)
        invariant forall x, y :: 0 <= x < y < i ==> cmp(a[x], a[y])
        
    {
        var j := i - 1;
        while j >= 0 && !cmp(a[j], a[j + 1])
            modifies a
            invariant forall x, y :: a !in cmp.reads(x, y)
            invariant forall x, y :: cmp.requires(x, y)
            invariant forall x, y :: cmp(x, y) || cmp(y, x)
            invariant forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z)
            invariant -1 <= j < i <= a.Length
            invariant forall x, y :: 0 <= x < y <= j ==> cmp(a[x], a[y])
            invariant forall x, y :: j < x < y <= i ==> cmp(a[x], a[y])
            invariant forall x, y :: 0 <= x < j + 1 < y <= i ==> cmp(a[x], a[y])
        {
            a[j], a[j+1] := a[j+1], a[j];
            j := j - 1;
        }
        i := i + 1;
    }
}

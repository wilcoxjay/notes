// RUN: /compile:0 /rlimit:1000000

method ArrayInit<A>(f: int -> A, a: array<A>)
    requires a != null
    requires forall x :: 0 <= x < a.Length ==> f.requires(x)
    requires forall x :: 0 <= x < a.Length ==> a !in f.reads(x)
    modifies a
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

class ArrayElementInitializer<Elt> {
    predicate Valid(i: int, a: Elt)
        reads this

    method Init(i: int) returns (a: Elt)
        modifies this
        ensures Valid(i, a)
        ensures forall x, y :: old(allocated(y)) && old(Valid(x, y)) ==> Valid(x, y)
}

method InitializeArray<Elt>(aei: ArrayElementInitializer<Elt>, a: array<Elt>)
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

    ensures max in a[..]
    ensures forall x :: 0 <= x < a.Length ==> cmp(a[x], max)
{
    max := a[0];
    var i := 0;
    while i < a.Length
        invariant max in a[..]
        invariant 0 <= i <= a.Length
        invariant forall x :: 0 <= x < i ==> cmp(a[x], max)
    {
        if !cmp(a[i], max) {
            max := a[i];
        }
        i := i + 1;
    }
}

method Set<A>(f: A -> bool, a: array<A>, i: int, x: A)
    requires a != null
    requires forall y :: a !in f.reads(y)
    requires forall j :: 0 <= j < a.Length ==> f.requires(a[j]) && f(a[j])
    requires 0 <= i < a.Length
    requires f.requires(x) && f(x)
    modifies a
    ensures forall y :: old(allocated(y)) ==> a !in f.reads(y)
    ensures forall j :: 0 <= j < a.Length ==> f.requires(a[j]) && f(a[j])
{
    a[i] := x;
}

method Insert<A>(cmp: (A, A) -> bool, a: array<A>, i: int)
    requires a != null
    requires forall x, y :: x in a[..] && y in a[..] ==> a !in cmp.reads(x, y)
    requires forall x, y :: x in a[..] && y in a[..] ==> cmp.requires(x, y)
    requires forall x, y :: x in a[..] && y in a[..] ==> cmp(x, y) || cmp(y, x)
    requires forall x, y, z :: x in a[..] && y in a[..] && z in a[..] ==> cmp(x, y) && cmp(y, z) ==> cmp(x, z)
    requires 0 <= i < a.Length
    requires forall x, y :: 0 <= x < y < i ==> cmp(a[x], a[y])
    modifies a
    ensures forall x :: 0 <= x < a.Length ==> a[x] in old(a[..])
    ensures forall x, y :: 0 <= x < y <= i ==> cmp(a[x], a[y])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var j := i - 1;
    while j >= 0 && !cmp(a[j], a[j + 1])
        modifies a
        invariant -1 <= j < i <= a.Length
        invariant forall x :: 0 <= x < a.Length ==> a[x] in old(a[..])
        invariant forall x, y :: 0 <= x < y <= j ==> cmp(a[x], a[y])
        invariant forall x, y :: j < x < y <= i ==> cmp(a[x], a[y])
        invariant forall x, y :: 0 <= x < j + 1 < y <= i ==> cmp(a[x], a[y])
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        a[j], a[j+1] := a[j+1], a[j];
        j := j - 1;
    }
}

method GenericSort<A>(cmp: (A, A) -> bool, a: array<A>)
    requires a != null
    requires forall x, y :: x in a[..] && y in a[..] ==> a !in cmp.reads(x, y)
    requires forall x, y :: x in a[..] && y in a[..] ==> cmp.requires(x, y)
    requires forall x, y :: x in a[..] && y in a[..] ==> cmp(x, y) || cmp(y, x)
    requires forall x, y, z :: x in a[..] && y in a[..] && z in a[..] ==> cmp(x, y) && cmp(y, z) ==> cmp(x, z)
    modifies a
    ensures forall x :: 0 <= x < a.Length ==> a[x] in old(a[..])
    ensures forall x, y :: 0 <= x < y < a.Length ==> cmp(a[x], a[y])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var i := 0;
    while i < a.Length
        modifies a
        invariant 0 <= i <= a.Length
        invariant forall x :: 0 <= x < a.Length ==> a[x] in old(a[..])
        invariant forall x, y :: 0 <= x < y < i ==> cmp(a[x], a[y])
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        Insert(cmp, a, i);
        i := i + 1;
    }
}

function method Range(start: int, length: nat): seq<int>
    decreases length
{
    if length == 0 then
        []
    else 
        [start] + Range(start + 1, length -1)
}

lemma lemma_RangeLength(start: int, length: nat)
    decreases length
    ensures |Range(start, length)| == length
{}

lemma lemma_RangeIndex(start: int, length: nat)
    decreases length
    ensures (lemma_RangeLength(start, length); forall i :: 0 <= i < length ==> Range(start, length)[i] == start + i)
{}

lemma lemma_SeqExt<A>(l1: seq<A>, l2: seq<A>)
    requires |l1| == |l2|
    requires forall i :: 0 <= i < |l1| ==> l1[i] == l2[i]
    ensures l1 == l2
{}

function Reverse<A>(l: seq<A>): seq<A>
{
    if l == [] then
        []
    else 
        Reverse(l[1..]) + [l[0]]
}

lemma lemma_ReverseLength<A>(l: seq<A>)
    ensures |Reverse(l)| == |l|
{}

lemma lemma_ReversePlus<A>(l1: seq<A>, l2: seq<A>)
    ensures Reverse(l1 + l2) == Reverse(l2) + Reverse(l1)
{
    if l1 != [] {
        assert (l1 + l2)[1..] == l1[1..] + l2;
    }
}

lemma lemma_ReverseIndex<A>(l: seq<A>, i: int)
    requires 0 <= i < |l|
    ensures (lemma_ReverseLength(l); Reverse(l)[i] == l[|l| - i - 1])
{
    lemma_ReverseLength(l);
}

lemma lemma_ReverseReverse<A>(l: seq<A>)
    ensures Reverse(Reverse(l)) == l
{
    lemma_ReverseLength(l);
    lemma_ReverseLength(Reverse(l));
    
    forall i | 0 <= i < |l| ensures Reverse(Reverse(l))[i] == l[i]
    {
        calc {
            Reverse(Reverse(l))[i]; 
                {lemma_ReverseIndex(Reverse(l), i);}
            Reverse(l)[|l| - i - 1];
                {lemma_ReverseIndex(l, |l| - i - 1);}
            l[i];
        }
    }

    lemma_SeqExt(Reverse(Reverse(l)), l);
}

lemma lemma_MultisetSeqRest<A>(l: seq<A>)
    requires l != []
    ensures multiset(l[1..]) == multiset(l) - multiset{l[0]}
{
    calc {
        multiset(l[1..]);
        multiset([l[0]] + l[1..]) - multiset{l[0]}; { assert l == [l[0]] + l[1..]; }
        multiset(l) - multiset{l[0]};
    }
}

lemma lemma_SortedUnique<A>(cmp: (A, A) -> bool, l1: seq<A>, l2: seq<A>)
    requires |l1| == |l2|
    requires multiset(l1) == multiset(l2)

    requires forall x, y :: x in l1 + l2 && y in l1 + l2 ==> cmp.requires(x, y)
    requires forall x :: x in l1 + l2 ==> cmp.requires(x, x) && cmp(x, x)
    requires forall x, y :: x in l1 + l2 && y in l1 + l2 ==> cmp(x, y) && cmp(y, x) ==> x == y

    requires forall x, y :: 0 <= x < y < |l1| ==> cmp(l1[x], l1[y])
    requires forall x, y :: 0 <= x < y < |l2| ==> cmp(l2[x], l2[y])
    
    ensures l1 == l2
{
    if l1 != [] {
        assert forall x :: x in l1 ==> cmp(l1[0], x);
        assert forall x :: x in l2 ==> cmp(l2[0], x);
        assert l1[0] in multiset(l2) && l2[0] in multiset(l1);
        assert cmp(l1[0], l2[0]) && cmp(l2[0], l1[0]);
        assert l1[0] == l2[0];
        calc {
            multiset(l1[1..]); 
                { lemma_MultisetSeqRest(l1); }
            multiset(l1) - multiset{l1[0]};
            multiset(l2) - multiset{l2[0]}; 
                { lemma_MultisetSeqRest(l2); }
            multiset(l2[1..]);
        }
        lemma_SortedUnique(cmp, l1[1..], l2[1..]);
    }
}

method Main(n: nat)
{
    var a := new int[n];
    ArrayInit((i: int) => i, a);

    lemma_RangeLength(0, n);
    lemma_RangeIndex(0, n);
    lemma_SeqExt(a[..], Range(0, n));
    assert a[..] == Range(0, n);
    
    var le := (x, y) => x <= y;
    GenericSort(le, a);
    lemma_SortedUnique(le, a[..], Range(0, n));
    assert a[..] == Range(0, n); 
}

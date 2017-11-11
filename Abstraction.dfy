// RUN: /compile:3 /rlimit:100000

abstract module ORDERED {
    type T
    predicate method le(a: T, b: T)

    lemma reflexive()
        ensures forall a :: le(a, a)

    lemma total()
        ensures forall a, b :: le(a, b) || le(b, a)

    lemma transitive()
        ensures forall a, b, c | le(a, b) && le(b, c) :: le(a, c)
}

abstract module Sort {
    export provides A, Sort, SortSorted
           reveals Sorted

    import A : ORDERED

    predicate Sorted(s: seq<A.T>)
    {
        forall i, j {:trigger A.le(s[i], s[j])} | 0 <= i <= j < |s| :: A.le(s[i], s[j])
    }

    function method Insert(a: A.T, s: seq<A.T>): seq<A.T>
    {
        if s == [] then
            [a]
        else if A.le(a, s[0]) then
            [a] + s
        else
            [s[0]] + Insert(a, s[1..])
    }

    function method Sort(s: seq<A.T>): seq<A.T>
    {
        if s == [] then
            []
        else
            Insert(s[0], Sort(s[1..]))
    }

    lemma InsertPerm(a: A.T, s: seq<A.T>)
        ensures multiset(Insert(a, s)) == multiset{a} + multiset(s)
    {
        if s == [] {
        } else if A.le(a, s[0]) {
        } else {
            var h := s[0];
            var t := s[1..];
            var i := Insert(a, t);
            calc {
                multiset([h] + i);
                multiset([h]) + multiset(i);
                multiset{h} + multiset(i);
                { InsertPerm(a, t); }
                multiset{h} + (multiset{a} + multiset(t));
                multiset{a} + multiset([h] + t);
                { assert s == [h] + t; }
                multiset{a} + multiset(s);
            }
        }
    }

    lemma InsertIn(a: A.T, s: seq<A.T>, x: A.T)
        requires x in Insert(a, s)
        ensures x == a || x in s
    {}

    lemma InsertSorted(a: A.T, s: seq<A.T>)
        requires Sorted(s)
        ensures Sorted(Insert(a, s))
    {
        A.reflexive();
        A.total();
        A.transitive();

        if s == [] {
        } else if A.le(a, s[0]) {
            var s' := [a] + s;
            forall i, j | 0 <= i <= j < |s'|
                ensures A.le(s'[i], s'[j])
            {
                if i == 0 {
                    if j > 0 {
                        assert A.le(s[0], s'[j]);
                    }
                }
            }
        } else {
            var s' := [s[0]] + Insert(a, s[1..]);
            InsertSorted(a, s[1..]);
            forall i, j | 0 <= i <= j < |s'|
                ensures A.le(s'[i], s'[j])
            {
                if i == 0 {
                    if j > 0 {
                        InsertIn(a, s[1..], s'[j]);
                        assert A.le(s'[i], s'[j]);
                    }
                }
            }
        }
    }

    lemma SortPerm(s: seq<A.T>)
        ensures multiset(Sort(s)) == multiset(s)
    {
        if s != [] {
            calc {
                multiset(Sort(s));
                multiset(Insert(s[0], Sort(s[1..])));
                { InsertPerm(s[0], Sort(s[1..])); }
                multiset{s[0]} + multiset(Sort(s[1..]));
                { SortPerm(s[1..]); }
                multiset{s[0]} + multiset(s[1..]);
                { assert s == [s[0]] + s[1..]; }
                multiset(s);
            }
        }
    }

    lemma SortSorted(s: seq<A.T>)
        ensures Sorted(Sort(s))
    {
        if s != [] {
            SortSorted(s[1..]);
            InsertSorted(s[0], Sort(s[1..]));
        }
    }
}


module IntOrdered refines ORDERED {
    type T = int
    predicate method le(a: T, b: T)
    {
        a <= b
    }

    lemma reflexive()
        ensures forall a :: le(a, a)
    {}

    lemma total()
        ensures forall a, b :: le(a, b) || le(b, a)
    {}

    lemma transitive()
        ensures forall a, b, c | le(a, b) && le(b, c) :: le(a, c)
    {}
}

module IntSort refines Sort {
    import A = IntOrdered
}

module RealOrdered refines ORDERED {
    type T = real

    predicate method le(a: T, b: T)
    {
        a <= b
    }

    lemma reflexive()
        ensures forall a :: le(a, a)
    {}

    lemma total()
        ensures forall a, b :: le(a, b) || le(b, a)
    {}

    lemma transitive()
        ensures forall a, b, c | le(a, b) && le(b, c) :: le(a, c)
    {}
}

module RealSort refines Sort {
    import A = RealOrdered
}

module Main {
    // import S = IntSort
    import S = RealSort
    method Main() {
        //var l := [3, 2, 1];
        var l := [3.0, 2.0, 1.0];
        var l' := S.Sort(l);
        print l';
    }
}

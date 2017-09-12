// RUN: /compile:0 /nologo /noNLarith /noCheating:1 /rlimit:1000000 /proc:*SiftUp*

module Relation {
    type T<A(==)> = iset<(A, A)>

    predicate Valid<A>(le: T<A>)
    {
        && (forall x, y, z ::
            && (x, y) in le
            && (y, z) in le
            ==> (x, z) in le)
        && (forall x, y :: (x, y) in le || (y, x) in le)
        && (forall x, y ::
            && (x, y) in le
            && (y, x) in le
            ==> x == y)
    }

    predicate Int(x: int, y: int) 
    {
        x <= y
    }
}

module Util {
    function SeqToMultiset<A>(l: seq<A>): multiset<A>
    {
        if l == [] then
            multiset{}
        else 
            multiset{l[0]} + SeqToMultiset(l[1..])
    }

    lemma SeqToMultisetAppend<A>(l1: seq<A>, l2: seq<A>)
        ensures SeqToMultiset(l1 + l2) == SeqToMultiset(l1) + SeqToMultiset(l2)
        ensures false
    {
        if l1 == [] {
        } else {
            calc {
                SeqToMultiset(l1 + l2);
                { assert l1 == [l1[0]] + l1[1..]; }
                SeqToMultiset(([l1[0]] + l1[1..]) + l2);
                { assert ([l1[0]] + l1[1..]) + l2 == [l1[0]] + (l1[1..] + l2); }
                SeqToMultiset([l1[0]] + (l1[1..] + l2));
                multiset{l1[0]} + SeqToMultiset(l1[1..] + l2);
                { SeqToMultisetAppend(l1[1..], l2); }
                multiset{l1[0]} + SeqToMultiset(l1[1..]) + SeqToMultiset(l2);
                SeqToMultiset(l1) + SeqToMultiset(l2);
            }
        }
    }
}

module PriorityQueueInternals {
    import Relation

    export 
        provides T, IsEmpty, IsValid, 
                 Contents, IsEmptyContents,
                 Size, IsEmptySize, SizeContents,
                 Empty, EmptyIsValid, EmptyContents,
                 Insert, InsertIsValid, InsertContents,
                 Pop, PopIsValid, PopContents, PopCorrect


        provides Relation

    datatype T<A> = Leaf | Node(data: A, left: T, right: T)

    predicate method IsEmpty(t: T)
    {
        t.Leaf?
    }

    function Size(t: T): nat
    {
        match t 
            case Leaf => 0
            case Node(_, l, r) => 1 + Size(l) + Size(r)
    }

    lemma IsEmptySize(t: T)
        ensures IsEmpty(t) <==> Size(t) == 0
    {}

    lemma IsEmptyContents(t: T)
        ensures IsEmpty(t) <==> Contents(t) == multiset{}
    {}

    predicate IsBalanced(t: T) 
    {
        match t
            case Leaf => true
            case Node(x, l, r) => 
                && Size(r) <= Size(l) <= Size(r) + 1
                && IsBalanced(l)
                && IsBalanced(r)
    }

    function Contents(t: T): multiset
    {
        match t
            case Leaf => multiset{}
            case Node(x, l, r) => multiset{x} + Contents(l) + Contents(r)
    }

    lemma SizeContents(t: T)
        ensures |Contents(t)| == Size(t)
    {}

    predicate IsHeap(le: Relation.T, t: T)
    {
        match t
            case Leaf => true
            case Node(x, l, r) => 
                && IsHeap(le, l)
                && IsHeap(le, r)
                && (forall y :: y in Contents(l) ==> (x, y) in le)
                && (forall y :: y in Contents(r) ==> (x, y) in le)
    }

    predicate IsValid(le: Relation.T, t: T)
    {
        && IsBalanced(t)
        && IsHeap(le, t)
    }

    predicate LeftBiasedLeaves(t: T)
    {
        match t
            case Leaf => true
            case Node(_, l, r) => 
                && (t.left.Leaf? ==> t.right.Leaf?)
                && LeftBiasedLeaves(l) 
                && LeftBiasedLeaves(r)
    }

    lemma IsBalancedImpliesLeftBiasedLeaves(t: T) 
        requires IsBalanced(t)
        ensures  LeftBiasedLeaves(t)
    {}


    function method Min<A>(le: Relation.T, x: A, y: A): A
    {
        if (x, y) in le then x else y
    }

    function method Max<A>(le: Relation.T, x: A, y: A): A
    {
        if (x, y) in le then y else x
    }

    function method Empty(): T
    {
        Leaf
    }

    lemma EmptyContents<A>()
        ensures Contents(Empty<A>()) == multiset{}
    {}

    lemma EmptyIsValid(le: Relation.T)
        requires Relation.Valid(le)
        ensures IsValid(le, Empty())
    {}

    function method Insert<A>(le: Relation.T, x: A, t: T): T
        decreases t
    {
        match t
            case Leaf => Node(x, Leaf, Leaf)
            case Node(y, l, r) => Node(Min(le, x, y), Insert(le, Max(le, x, y), r), l)
    }

    lemma InsertContents<A>(le: Relation.T, x: A, t: T)
        requires Relation.Valid(le)
        ensures Contents(Insert(le, x, t)) == Contents(t) + multiset{x}
        decreases t
    {
        match t 
            case Leaf => {}
            case Node(y, l, r) => {
                InsertContents(le, Max(le, x, y), r);
            }
    }

    lemma InsertIsBalanced<A>(le: Relation.T, x: A, t: T)
        requires IsBalanced(t)
        requires Relation.Valid(le)
        ensures  IsBalanced(Insert(le, x, t))
        decreases t
    {
        match t
            case Leaf => 
            case Node(y, l, r) =>
                InsertContents(le, Max(le, x, y), r);
                InsertIsBalanced(le, Max(le, x, y), r);
                SizeContents(Insert(le, x, t));
                SizeContents(t);
    }

    lemma MinLe2<A>(le: Relation.T<A>, x: A, y: A)
        requires Relation.Valid(le)
        ensures (Min(le, x, y), y) in le
    {

    }

    lemma MinLeMax<A>(le: Relation.T<A>, x: A, y: A)
        requires Relation.Valid(le)
        ensures (Min(le, x, y), Max(le, x, y)) in le
    {
    }

    lemma InsertIsHeap<A>(le: Relation.T, x: A, t: T)
        requires Relation.Valid(le)
        requires IsHeap(le, t)
        ensures  IsHeap(le, Insert(le, x, t))
        decreases t
    {
        match t 
            case Leaf => 
            case Node(y, l, r) =>
                InsertIsHeap(le, Max(le, x, y), r);
                InsertContents(le, Max(le, x, y), r);
                forall z | z in Contents(Insert(le, Max(le, x, y), r)) 
                    ensures (Min(le, x, y), z) in le
                {
                    assert z in Contents(r) + multiset{Max(le, x, y)};
                    if z in Contents(r) {
                        assert (y, z) in le;
                        MinLe2(le, x, y);
                    } else {
                        assert z == Max(le, x, y);
                        MinLeMax(le, x, y);
                    }
                }
    }

    lemma InsertIsValid<A>(le: Relation.T, x: A, t: T)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures  IsValid(le, Insert(le, x, t))
    {
        InsertIsBalanced(le, x, t);
        InsertIsHeap(le, x, t);
    }

    function method DeleteLeft<A>(le: Relation.T, t: T): (A, T)
        requires !IsEmpty(t)
        requires LeftBiasedLeaves(t)
    {
        match t
            case Node(x, l, r) => 
                if l.Leaf? then
                    (x, Leaf)
                else 
                    var (y, l') := DeleteLeft(le, l); 
                    (y, Node(x, r, l'))
    }

    lemma DeleteLeftContents(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires LeftBiasedLeaves(t)
        ensures var (y, t') := DeleteLeft(le, t); Contents(t) == Contents(t') + multiset{y}
    {
        match t
            case Node(x, l, r) => 
                if l.Leaf? {
                } else {
                    var (y, l') := DeleteLeft(le, l); 
                }
    }

    lemma DeleteLeftIsBalanced(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires IsBalanced(t)
        ensures  (IsBalancedImpliesLeftBiasedLeaves(t); var (_, t') := DeleteLeft(le, t); IsBalanced(t'))
    {
        IsBalancedImpliesLeftBiasedLeaves(t);
        match t
            case Node(x, l, r) => 
                if !l.Leaf? {
                    DeleteLeftContents(le, l);
                    var (y, l') := DeleteLeft(le, l); 
                    SizeContents(l');
                    SizeContents(l);
                }
    }

    lemma DeleteLeftIsHeap(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires LeftBiasedLeaves(t)
        requires Relation.Valid(le)
        requires IsHeap(le, t)
        ensures  (var (_, t') := DeleteLeft(le, t); IsHeap(le, t'))
    {
        match t
            case Node(x, l, r) => 
                if !l.Leaf? {
                    var (_, l') := DeleteLeft(le, l);
                    DeleteLeftContents(le, l);
                    forall y | y in Contents(l') 
                        ensures (x, y) in le
                    {
                        assert y in Contents(l);
                    }
                }
    }


    lemma DeleteLeftIsValid(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures  (IsBalancedImpliesLeftBiasedLeaves(t); var (_, t') := DeleteLeft(le, t); IsValid(le, t'))
    {
        DeleteLeftIsBalanced(le, t);
        IsBalancedImpliesLeftBiasedLeaves(t);
        DeleteLeftIsHeap(le, t);
    }


    function method SiftDown<A>(le: Relation.T, a: A, l: T, r: T): T
        decreases Size(l) + Size(r)
    {
        match l 
            case Leaf => Node(a, Leaf, Leaf)
            case Node(x1, l1, r1) => 
                match r 
                    case Leaf => Node(Min(le, a, x1), Node(Max(le, x1, a), Leaf, Leaf), Leaf)
                    case Node(x2, l2, r2) => 
                        if (a, x1) in le && (a, x2) in le then
                            Node(a, l, r)
                        else if (x1, x2) in le then
                            Node(x1, SiftDown(le, a, l1, r1), Node(x2, l2, r2))
                        else 
                            Node(x2, Node(x1, l1, r1), SiftDown(le, a, l2, r2))
    }

    lemma SiftDownContents<A>(le: Relation.T, a: A, l: T, r: T)
        decreases Size(l) + Size(r)
        requires IsBalanced(Node(a, l, r))
        requires Relation.Valid(le)
        ensures Contents(SiftDown(le, a, l, r)) == multiset{a} + Contents(l) + Contents(r)
    {
        match l 
            case Leaf => {}
            case Node(x1, l1, r1) => 
                match r 
                    case Leaf => 
                    case Node(x2, l2, r2) => 
                        SiftDownContents(le, a, l1, r1); 
                        SiftDownContents(le, a, l2, r2); 
    }

    lemma SiftDownIsBalanced<A>(le: Relation.T, a: A, l: T, r: T)
        decreases Size(l) + Size(r)
        requires IsBalanced(Node(a, l, r))
        requires Relation.Valid(le)
        ensures  IsBalanced(SiftDown(le, a, l, r))
    {
        match l 
            case Leaf => {}
            case Node(x1, l1, r1) => 
                match r 
                    case Leaf => {}
                    case Node(x2, l2, r2) =>
                        if (a, x1) in le && (a, x2) in le {
                        } else if (x1, x2) in le {
                            SiftDownIsBalanced(le, a, l1, r1);
                            SiftDownContents(le, a, l1, r1);
                            SizeContents(SiftDown(le, a, l1, r1));
                            SizeContents(l1);
                            SizeContents(r1);
                        } else {
                            SiftDownIsBalanced(le, a, l2, r2);
                            SiftDownContents(le, a, l2, r2);
                            SizeContents(SiftDown(le, a, l2, r2));
                            SizeContents(l2);
                            SizeContents(r2);
                        }
    }

    lemma SiftDownIsHeap<A>(le: Relation.T, a: A, l: T, r: T)
        decreases Size(l) + Size(r)
        requires Relation.Valid(le)
        requires IsBalanced(Node(a, l, r))
        requires IsHeap(le, l)
        requires IsHeap(le, r)
        ensures  IsHeap(le, SiftDown(le, a, l, r))
    {
        SiftDownContents(le, a, l, r);
        match l 
            case Leaf => {}
            case Node(x1, l1, r1) => 
                match r 
                    case Leaf => {}
                    case Node(x2, l2, r2) => 
                        if (a, x1) in le && (a, x2) in le {
                        } else if (x1, x2) in le {
                            SiftDownIsHeap(le, a, l1, r1);
                            SiftDownContents(le, a, l1, r1);
                            SizeContents(SiftDown(le, a, l1, r1));
                            SizeContents(l1);
                            SizeContents(r1);
                        } else {
                            SiftDownIsHeap(le, a, l2, r2);
                            SiftDownContents(le, a, l2, r2);
                            SizeContents(SiftDown(le, a, l2, r2));
                            SizeContents(l2);
                            SizeContents(r2);
                        }
    }

    lemma SiftDownIsValid<A>(le: Relation.T, a: A, l: T, r: T)
        requires IsBalanced(Node(a, l, r))
        requires Relation.Valid(le)
        requires IsHeap(le, l)
        requires IsHeap(le, r)

        ensures  IsValid(le, SiftDown(le, a, l, r))
    {
        SiftDownIsBalanced(le, a, l, r);
        SiftDownIsHeap(le, a, l, r);
    }

    function method RemoveMin(le: Relation.T, t: T): T
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires LeftBiasedLeaves(t)
    {
        if t.left.Leaf? then
            Leaf
        else 
            var (y, l') := DeleteLeft(le, t.left); 
            SiftDown(le, y, t.right, l')
    }

    lemma RemoveMinIsValid(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures  (IsBalancedImpliesLeftBiasedLeaves(t); IsValid(le, RemoveMin(le, t)))
    {
        IsBalancedImpliesLeftBiasedLeaves(t);
        if !t.left.Leaf? {
            DeleteLeftIsBalanced(le, t.left);
            DeleteLeftIsHeap(le, t.left);
            DeleteLeftContents(le, t.left);
            SizeContents(t.left);
            var (y, l') := DeleteLeft(le, t.left); 
            SizeContents(l');
            SiftDownIsValid(le, y, t.right, l');
        }
    }

    lemma RemoveMinContents(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires IsBalanced(t)
        requires Relation.Valid(le)
        ensures (IsBalancedImpliesLeftBiasedLeaves(t); Contents(RemoveMin(le, t)) + multiset{t.data} == Contents(t))
    {
        IsBalancedImpliesLeftBiasedLeaves(t);
        if !t.left.Leaf? {
            DeleteLeftIsBalanced(le, t.left);
            DeleteLeftContents(le, t.left);
            SizeContents(t.left);
            var (y, l') := DeleteLeft(le, t.left);
            SizeContents(t.right);
            SizeContents(l');
            SiftDownContents(le, y, t.right, l');
        }
    }

    function method Pop<A>(le: Relation.T, t: T): (A, T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
    {
        (t.data, IsBalancedImpliesLeftBiasedLeaves(t); RemoveMin(le, t))
    }

    lemma PopIsValid(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures  var (_, t') := Pop(le, t); IsValid(le, t')
    {
        IsBalancedImpliesLeftBiasedLeaves(t);
        RemoveMinIsValid(le, t);
    }

    lemma PopContents(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures var (y, t') := Pop(le, t); Contents(t) == multiset{y} + Contents(t')
    {
        RemoveMinContents(le, t);
    }

    lemma RootIsMin(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures forall z :: z in Contents(t) ==> (t.data, z) in le
    {}

    lemma PopCorrect(le: Relation.T, t: T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures var (y, t') := Pop(le, t); forall z :: z in Contents(t') ==> (y, z) in le
    {
        var (y, t') := Pop(le, t);
        RootIsMin(le, t);
        forall z | z in Contents(t') 
            ensures (y, z) in le
        {
            assert z in Contents(t);
        }
    }
}

module PriorityQueue {
    export provides T, IsValid, Contents, IsEmpty, Empty, Insert, Pop
           provides Relation

    import PQ = PriorityQueueInternals
    import Relation

    type T<A> = PQ.T<A>

    predicate IsValid(le: Relation.T, t: T)
        requires Relation.Valid(le)
    {
        PQ.IsValid(le, t)
    }

    function Contents(t: T): multiset
    {
        PQ.Contents(t)
    }

    function Size(t: T): nat
    {
        PQ.Size(t)
    }

    predicate method IsEmpty(t: T)
        ensures IsEmpty(t) <==> Contents(t) == multiset{}
    {
        PQ.IsEmptyContents(t);
        PQ.IsEmpty(t)
    }

    lemma EmptyIsValidAll<A>()
        ensures forall le: Relation.T<A> :: Relation.Valid(le) ==> IsValid(le, PQ.Empty<A>())
    {
        forall le: Relation.T<A> | Relation.Valid(le)
            ensures IsValid<A>(le, PQ.Empty())
        { 
            PQ.EmptyIsValid(le);
        }
    }

    function method Empty<A>(): T<A>
        ensures forall le: Relation.T<A> :: Relation.Valid(le) ==> IsValid(le, Empty())
        ensures Contents(Empty<A>()) == multiset{}
    {
        EmptyIsValidAll<A>();
        PQ.EmptyContents<A>();
        PQ.Empty()
    }

    function method Insert<A>(le: Relation.T, x: A, t: T): T
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures  IsValid(le, Insert(le, x, t))
        ensures  Contents(Insert(le, x, t)) == multiset{x} + Contents(t)
    {
        PQ.InsertIsValid(le, x, t);
        PQ.InsertContents(le, x, t);
        PQ.Insert(le, x, t)
    }

    function method Pop<A>(le: Relation.T, t: T): (A, T)
        requires !IsEmpty(t)
        requires Relation.Valid(le)
        requires IsValid(le, t)
        ensures  (var (y, t') := Pop(le, t); 
                   && IsValid(le, t')
                   && Contents(t') + multiset{y} == Contents(t)
                   && (forall z :: z in Contents(t') ==> (y, z) in le))
    {
        PQ.PopIsValid(le, t);
        PQ.PopContents(le, t);
        PQ.PopCorrect(le, t);
        PQ.Pop(le, t)
    }
}

module PQSort {
    import PQ = PriorityQueue
    import Relation
    import Util

    function method InsertAll(le: Relation.T, l: seq, pq : PQ.T): PQ.T
        requires Relation.Valid(le)
        requires PQ.IsValid(le, pq)
        ensures PQ.IsValid(le, InsertAll(le ,l, pq))
    {
        if l == [] then
            pq
        else 
            InsertAll(le, l[1..], PQ.Insert(le, l[0], pq))
    }

    lemma InsertAllContents(le: Relation.T, l: seq, pq: PQ.T)
        requires Relation.Valid(le)
        requires PQ.IsValid(le, pq)
        ensures PQ.Contents(InsertAll(le, l, pq)) == Util.SeqToMultiset(l) + PQ.Contents(pq)
    {}

    function method PopAll(le: Relation.T, pq: PQ.T): seq
        requires Relation.Valid(le)
        decreases |PQ.Contents(pq)|
        requires PQ.IsValid(le, pq)
    {
        if PQ.IsEmpty(pq) then
            []
        else 
            var (x, pq') := PQ.Pop(le, pq);
            [x] + PopAll(le, pq')
    }

    lemma PQContentsPopAll(le: Relation.T, pq: PQ.T)
        requires Relation.Valid(le)
        requires PQ.IsValid(le, pq)
        ensures Util.SeqToMultiset(PopAll(le, pq)) == PQ.Contents(pq)
        decreases |PQ.Contents(pq)|
    {
        if PQ.IsEmpty(pq) {
        } else {
            var (x, pq') := PQ.Pop(le, pq);
            PQContentsPopAll(le, pq');
        }
    }

    lemma PQInContentsInPopAll<A>(le: Relation.T<A>, pq: PQ.T<A>, x: A) 
        requires Relation.Valid(le)
        requires PQ.IsValid(le, pq)
        ensures  x in PQ.Contents(pq) <==> x in PopAll(le, pq)
        decreases |PQ.Contents(pq)|
    {
        if PQ.IsEmpty(pq) {
        } else {
            var (x, pq') := PQ.Pop(le, pq);
        }
    }

    predicate Sorted<A>(le: Relation.T<A>, l: seq<A>)
        requires Relation.Valid(le)
    {
        forall i, j :: 0 <= i < j < |l| ==> (l[i], l[j]) in le
    }

    lemma PopAllSorted(le: Relation.T, pq: PQ.T)
        requires Relation.Valid(le)
        requires PQ.IsValid(le, pq)
        ensures Sorted(le, PopAll(le, pq))
        decreases |PQ.Contents(pq)|
    {
        if PQ.IsEmpty(pq) {
        } else {
            var (x, pq') := PQ.Pop(le, pq);
            PopAllSorted(le, pq');
            var l := [x] + PopAll(le, pq');
            forall i, j | 0 <= i < j < |l|
                ensures (l[i], l[j]) in le
            {
                PQInContentsInPopAll(le, pq', l[j]);
            }
        }
    }

    function method Sort<A>(le: Relation.T<A>, l: seq<A>): seq<A>
        requires Relation.Valid(le)
        ensures Sorted(le, Sort(le, l))
        ensures Util.SeqToMultiset(l) == Util.SeqToMultiset(Sort(le, l))
    {
        var pq := InsertAll(le, l, PQ.Empty());
        PopAllSorted(le, pq);
        PQContentsPopAll(le, pq);
        InsertAllContents(le, l, PQ.Empty());
        PopAll(le, pq)
    }
}

module ArrayPQ {
    import Util

    trait HasTime {
        var time: real
    }

    function ArrayContents(a: array<HasTime>): multiset<HasTime>
        reads a
        requires a != null
    {
        Util.SeqToMultiset(a[..])
    }


    predicate IsHeap(a: array<HasTime>)
        reads a
        requires a != null
        reads set i | 0 <= i < a.Length :: a[i]
        requires forall i :: 0 <= i < a.Length ==> a[i] != null
    {
        forall i, j ::
            && (j == 2 * i + 1 || j == 2 * i)
            && 0 <= i < a.Length
            && 0 <= j < a.Length
            ==> a[i].time <= a[j].time
    }

    lemma SequenceSplit2<A>(s: seq<A>, i: int, j: int)
        requires 0 <= i < j < |s|
        ensures s == s[0..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..]
    {}

    method SiftUp(a: array<HasTime>, k: int)
        requires a != null
        requires forall i :: 0 <= i < a.Length ==> a[i] != null
        requires 0 <= k < a.Length
        requires
            forall i, j ::
                && (j == 2 * i + 1 || j == 2 * i)
                && 0 <= i < a.Length
                && 0 <= j < a.Length
                && j != k
                ==> a[i].time <= a[j].time

        modifies a
        ensures forall i :: 0 <= i < a.Length ==> a[i] != null
        ensures ArrayContents(a) == old(ArrayContents(a))
        ensures IsHeap(a)
    {
        var k' := k;

        while k' > 0
            invariant 0 <= k' < a.Length
            invariant forall i :: 0 <= i < a.Length ==> a[i] != null
            invariant ArrayContents(a) == old(ArrayContents(a))
            invariant
                forall i, j ::
                    && (j == 2 * i + 1 || j == 2 * i)
                    && 0 <= i < a.Length
                    && 0 <= j < a.Length
                    && j != k'
                    ==> a[i].time <= a[j].time
            modifies a
        {
            var parent := k' / 2;
            assert 0 <= parent < a.Length;
            if a[parent].time <= a[k'].time {
                break;
            }
            ghost var old_a := a[..];
            assert old_a[parent].time > old_a[k'].time;
            a[parent], a[k'] := a[k'], a[parent];
            assert old_a[parent].time > old_a[k'].time;
            assert forall i :: 0 <= i < a.Length ==> a[i] != null;
            calc {
                ArrayContents(a);
                Util.SeqToMultiset(a[..]);
                {
                    SequenceSplit2(a[..], parent, k');
                }
                Util.SeqToMultiset(a[0..parent] + [a[parent]] + a[parent+1..k'] + [a[k']] + a[k'+1..]);
                {
                    Util.SeqToMultisetAppend(a[0..parent] + [a[parent]] + a[parent+1..k'] + [a[k']], a[k'+1..]);
                    Util.SeqToMultisetAppend(a[0..parent] + [a[parent]] + a[parent+1..k'] , [a[k']]);
                    Util.SeqToMultisetAppend(a[0..parent] + [a[parent]] , a[parent+1..k']);
                    Util.SeqToMultisetAppend(a[0..parent] , [a[parent]]);
                }
                Util.SeqToMultiset(a[0..parent]) + Util.SeqToMultiset([a[parent]])
                    + Util.SeqToMultiset(a[parent+1..k']) + Util.SeqToMultiset([a[k']])
                    + Util.SeqToMultiset(a[k'+1..]);
                {
                    assert Util.SeqToMultiset([a[parent]]) == multiset{a[parent]};
                    assert Util.SeqToMultiset([a[k']]) == multiset{a[k']};
                }
                Util.SeqToMultiset(a[0..parent]) + multiset{a[parent]}
                    + Util.SeqToMultiset(a[parent+1..k']) + multiset{a[k']}
                    + Util.SeqToMultiset(a[k'+1..]);
                {
                    assert a[0..parent] == old_a[0..parent];
                    assert a[parent] == old_a[k'] ;
                    assert a[parent+1..k'] == old_a[parent+1..k'];
                    assert a[k'] == old_a[parent];
                    assert a[k'+1..] == old_a[k'+1..];
                }
                Util.SeqToMultiset(old_a[0..parent]) + multiset{old_a[parent]} + Util.SeqToMultiset(old_a[parent+1..k']) + multiset{old_a[k']} + Util.SeqToMultiset(old_a[k'+1..]);
                {
                    assert Util.SeqToMultiset([old_a[parent]]) == multiset{old_a[parent]};
                    assert Util.SeqToMultiset([old_a[k']]) == multiset{old_a[k']};
                }
                Util.SeqToMultiset(old_a[0..parent]) + Util.SeqToMultiset([old_a[parent]])
                    + Util.SeqToMultiset(old_a[parent+1..k']) + Util.SeqToMultiset([old_a[k']])
                    + Util.SeqToMultiset(old_a[k'+1..]);
                {
                    Util.SeqToMultisetAppend(old_a[0..parent] + [old_a[parent]] + old_a[parent+1..k'] + [old_a[k']], old_a[k'+1..]);
                    Util.SeqToMultisetAppend(old_a[0..parent] + [old_a[parent]] + old_a[parent+1..k'] , [old_a[k']]);
                    Util.SeqToMultisetAppend(old_a[0..parent] + [old_a[parent]] , old_a[parent+1..k']);
                    Util.SeqToMultisetAppend(old_a[0..parent] , [old_a[parent]]);
                }
                Util.SeqToMultiset(old_a[0..parent] + [old_a[parent]] + old_a[parent+1..k'] + [old_a[k']] + old_a[k'+1..]); { SequenceSplit2(old_a, parent, k'); }
                Util.SeqToMultiset(old_a);
            }
            forall i, j | && (j == 2 * i + 1 || j == 2 * i)
                          && 0 <= i < a.Length
                          && 0 <= j < a.Length
                          && j != parent
                ensures a[i].time <= a[j].time
            {
                if j == k' {
                    assert i == parent;
                    assert a[parent] == old_a[k'];
                    assert a[k'] == old_a[parent];
                    assert old_a[parent].time > old_a[k'].time;
                    assert a[parent].time <= a[k'].time;
                } else {
                    assert a[i].time <= a[j].time;
                }
            }

            k' := parent;
        }
    }

    class PriorityQueue {
        var data: array<HasTime>

        constructor PriorityQueue()
            ensures Valid()
        {
            data := new HasTime[0];
        }

        predicate Valid()
            reads this
        {
            data != null
        }

        function Contents(): multiset<HasTime>
            reads this, data
            requires Valid()
        {
            ArrayContents(data)
        }



        method Insert(x: HasTime)
            requires Valid()
            ensures Valid()
            ensures Contents() == old(Contents()) + multiset{x}
        {

        }
    }
}

module DES {
    import PQ = PriorityQueue

    class Simulator {
        var queue: PQ.T<Event>
        var time: real

        method Schedule(ev: Event)
            modifies this
            requires ev != null && time <= ev.time
        {
        }

        method Loop()
            decreases *
        {
//            var le := iset e1: Event, e2: Event | e1.time <= e2.time :: (e1, e2);

            while !PQ.IsEmpty(queue)
                decreases *
            {
  //              var (ev, q) := PQ.Pop(le, queue);
            }
        }
    }

    class Event {
        var time: real

        method Execute(sim: Simulator)
            requires sim != null && sim.time == time
            modifies sim
    }
} 

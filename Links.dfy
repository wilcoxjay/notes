// RUN: /compile:0 /rlimit:500000 /print:log.bpl

module Prelude {
    function method Max(a: int, b: int): int
    {
        if a > b then a else b
    }

    lemma Foo(x: int, d: int)
        requires d > 0
        ensures x % d >= 0
    {
        assert (-1) % 3 == 2;
    }

    function method Last<T>(l: seq<T>): T
        requires |l| > 0
    {
        l[|l| - 1]
    }
}

module Array {
    export provides Copy

    method Copy1<T>(dst: array<T>, dst_start: int, src: array<T>, src_start: int, n: int)
        requires dst != null && 0 <= dst_start && dst_start + n <= dst.Length
        requires src != null && 0 <= src_start && src_start + n <= src.Length
        requires n >= 0
        requires dst == src ==> dst_start <= src_start
        modifies dst
        ensures dst[dst_start..dst_start+n] == old(src[src_start..src_start+n])
        ensures dst[..dst_start] == old(dst[..dst_start])
        ensures dst[dst_start+n..] == old(dst[dst_start+n..])
    {
        var i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant dst[dst_start..dst_start+i] == old(src[src_start..src_start+i])
            invariant dst[..dst_start] == old(dst[..dst_start])
            invariant dst[dst_start+i..] == old(dst[dst_start+i..])
        {
            dst[dst_start + i] := src[src_start + i];
            i := i + 1;
        }
    }


    method Copy2<T>(dst: array<T>, dst_start: int, src: array<T>, src_start: int, n: int)
        requires dst != null && 0 <= dst_start && dst_start + n <= dst.Length
        requires src != null && 0 <= src_start && src_start + n <= src.Length
        requires n >= 0
        requires dst == src ==> dst_start >= src_start
        modifies dst
        ensures dst[dst_start..dst_start+n] == old(src[src_start..src_start+n])
        ensures dst[..dst_start] == old(dst[..dst_start])
        ensures dst[dst_start+n..] == old(dst[dst_start+n..])
    {
        var i := n - 1;
        while i >= 0
            invariant -1 <= i <= n
            invariant dst[dst_start+i+1..dst_start+n] == old(src[src_start+i+1..src_start+n])
            invariant dst[..dst_start+i+1] == old(dst[..dst_start+i+1])
            invariant dst[dst_start+n..] == old(dst[dst_start+n..])
        {
            dst[dst_start + i] := src[src_start + i];
            i := i - 1;
        }
    }

    method Copy<T>(dst: array<T>, dst_start: int, src: array<T>, src_start: int, n: int)
        requires dst != null && 0 <= dst_start && dst_start + n <= dst.Length
        requires src != null && 0 <= src_start && src_start + n <= src.Length
        requires n >= 0
        modifies dst
        ensures dst[dst_start..dst_start+n] == old(src[src_start..src_start+n])
        ensures dst[..dst_start] == old(dst[..dst_start])
        ensures dst[dst_start+n..] == old(dst[dst_start+n..])
    {
        if {
            case dst_start <= src_start => Copy1(dst, dst_start, src, src_start, n);
            case dst_start >= src_start => Copy2(dst, dst_start, src, src_start, n);
        }
    }

    method IndexOf<T(==)>(a: array<T>, i_min: int, i_max: int, x: T) returns (i: int)
        requires a != null && 0 <= i_min <= i_max <= a.Length
        ensures i >= i_min ==> i < i_max && a[i] == x
        ensures i < i_min ==> x !in a[i_min..i_max]
    {
        i := i_min;
        while i < i_max
            invariant i_min <= i <= i_max
            invariant x !in a[i_min..i]
        {
            if a[i] == x { return; }
            i := i + 1;
        }

        return i_min - 1;
    }

    predicate Sorted(a: array<int>)
        reads a
        requires a != null
    {
        forall i | 0 <= i < a.Length - 1 :: a[i] <= a[i+1]
    }

    lemma SortedAllIndices(a: array<int>, i: int, j: int)
        requires a != null && Sorted(a) && 0 <= i <= j < a.Length
        ensures a[i] <= a[j]
        decreases j - i
    {
        if i != j {
            SortedAllIndices(a, i + 1, j);
        }
    }

    method BinarySearch(a: array<int>, x: int) returns (i: int)
        requires a != null && Sorted(a)
        ensures 0 <= i <= a.Length
        ensures forall j | 0 <= j < i && j < a.Length :: a[j] <= x
        ensures forall j | i <= j < a.Length :: a[j] >= x
    {
        var lo, hi := 0, a.Length;
        while lo + 1 < hi
            invariant 0 <= lo <= hi <= a.Length
            invariant forall j | 0 <= j < lo :: a[j] <= x
            invariant forall j | hi <= j < a.Length :: a[j] >= x
        {
            var mid := (lo + hi) / 2;
            if {
                case a[mid] < x =>
                    lo := mid + 1;
                    forall j | 0 <= j < lo
                        ensures a[j] <= x
                    {
                        SortedAllIndices(a, j, mid);
                    }
                case a[mid] == x =>
                    forall j | 0 <= j <= mid
                        ensures a[j] <= x
                    {
                        SortedAllIndices(a, j, mid);
                    }
                    forall j | mid <= j < a.Length
                        ensures a[j] >= x
                    {
                        SortedAllIndices(a, mid, j);
                    }
                    return mid;
                case a[mid] > x =>
                    hi := mid;
                    forall j | hi <= j < a.Length
                        ensures a[j] >= x
                    {
                        SortedAllIndices(a, mid, j);
                    }

            }
        }
        if lo == hi {
            return lo;
        } else {
            assert lo + 1 == hi;
            if a[lo] <= x {
                return lo + 1;
            } else {
                return lo;
            }
        }
    }
}

module Slice {
    class Slice<T> {
        var buf: array<T>
        var start: int
        var length: int

        ghost var contents: seq<T>

        predicate Valid()
            reads this, buf
        {
            && buf != null
            && 0 <= start <= buf.Length
            && 0 <= length
            && start + length <= buf.Length
        }
    }
}

module List {
    import Prelude
    export provides List, List.repr, List.contents, List.Valid,
                    List.PushFront, List.PushBack, List.PopFront, List.PopBack,
                    List.Index, List.List

    class Node<T> {
        var next: Node<T>
        var data: T

        constructor(data: T, next: Node<T>)
            ensures this.data == data && this.next == next
        {
            this.next := next;
            this.data := data;
        }
    }

    class List<T> {
        var head: Node<T>
        var tail: Node<T>

        ghost var repr: set<object>
        ghost var spine: seq<Node<T>>
        ghost var contents: seq<T>


        constructor List()
            ensures Valid() && contents == [] && repr == {}
        {
            head := null;
            tail := null;
            repr := {};
            spine := [];
            contents := [];
        }

        predicate Valid()
            reads this, repr
            ensures Valid() ==> null !in repr
        {
            && null !in repr
            && this !in repr
            && ((head == null) == (tail == null) == (spine == []))
            && |spine| == |contents|
            && (head != null ==> spine[0] == head)
            && (tail != null ==> Prelude.Last(spine) == tail)
            && (forall i {:trigger spine[i] in repr} {:trigger spine[i].data} {:trigger spine[i].next}| 0 <= i < |spine| ::
                && spine[i] in repr
                && spine[i].data == contents[i]
                && spine[i].next == (if i < |spine| - 1 then spine[i+1] else null))
        }

        method PushFront(x: T)
            requires Valid()
            modifies this, repr
            ensures Valid() && fresh(repr - old(repr)) && contents == [x] + old(contents)
        {
            var node := new Node(x, head);
            head := node;
            if tail == null {
                tail := node;
            }
            repr := repr + {node};
            spine := [node] + spine;
            contents := [x] + contents;
        }

        method PushBack(x: T)
            requires Valid()
            modifies this, repr
            ensures Valid() && fresh(repr - old(repr)) && contents == old(contents) + [x]
        {
            var node := new Node(x, null);
            if tail == null {
                head := node;
            } else {
                tail.next := node;
            }
            tail := node;
            repr := repr + {node};
            spine := spine + [node];
            contents := contents + [x];
        }

        method PopFront() returns (x: T)
            requires Valid() && |contents| > 0
            modifies this, repr
            ensures Valid() && fresh(repr - old(repr)) && [x] + contents == old(contents)
        {
            x := head.data;
            head := head.next;
            if head == null {
                tail := null;
            }
            contents := contents[1..];
            spine := spine[1..];
        }

        method PopBack() returns (x: T)
            requires Valid() && |contents| > 0
            modifies this, repr
            ensures Valid() && fresh(repr - old(repr)) && contents + [x] == old(contents)
        {
            x := tail.data;
            contents := contents[..|contents|-1];
            spine := spine[..|spine|-1];

            if head == tail {
                head := null;
                tail := null;
                return;
            }

            var node := head;
            ghost var i := 0;
            while node.next != tail
                invariant 0 <= i < |spine|
                invariant node == spine[i]
                decreases |spine| - i
            {
                node := node.next;
                i := i + 1;
            }

            tail := node;
            tail.next := null;
        }

        method Index(i: int) returns (x: T)
            requires Valid() && 0 <= i < |contents|
            ensures x == contents[i]
        {
            var j := 0;
            var node := head;

            while j < i
                invariant 0 <= j <= i
                invariant node == spine[j]
            {
                node := node.next;
                j := j + 1;
            }

            x := node.data;
        }
    }
}

module DoublyLinkedList {
    import Prelude

    export provides List, List.List, List.Valid, List.repr, List.contents,
                    List.PushBack

    class Node<T> {
        var prev: Node<T>
        var next: Node<T>
        var data: T

        constructor(data: T)
            ensures this.data == data
        {
            this.data := data;
        }
    }

    class List<T> {
        var head: Node<T>
        var tail: Node<T>

        ghost var repr: set<object>
        ghost var spine: seq<Node<T>>
        ghost var contents: seq<T>

        constructor List()
            ensures Valid() && fresh(repr) && contents == []
        {
            head := null;
            tail := null;
            repr := {};
            spine := [];
            contents := [];
        }

        predicate Valid()
            reads this, repr
            ensures Valid() ==> null !in repr
        {
            && ((head == null) == (tail == null) == (|spine| == 0))
            && null !in repr
            && this !in repr
            && |spine| == |contents|
            && (forall i {:trigger spine[i].next} {:trigger spine[i].prev} {:trigger spine[i].data} {:trigger spine[i] in repr} | 0 <= i < |spine| ::
                && spine[i] in repr
                && spine[i].data == contents[i]
                && (spine[i].next == (if i < |spine| - 1 then spine[i+1] else null))
                && (spine[i].prev == (if i > 0 then spine[i-1] else null)))
            && (head != null ==> head == spine[0])
            && (tail != null ==> tail == Prelude.Last(spine))
        }

        method PushFront(x: T)
            requires Valid()
            modifies this, repr
            ensures Valid() && contents == [x] + old(contents)
        {
            var node := new Node(x);
            node.next := head;
            node.prev := null;

            if head == null {
                tail := node;
            } else {
                node.next.prev := node;
            }

            head := node;
            spine := [node] + spine;
            contents := [x] + contents;
            repr := repr + {node};
        }

        method PushBack(x: T)
            requires Valid()
            modifies this, repr
            ensures Valid() && fresh(repr - old(repr)) && contents == old(contents) + [x]
        {
            var node := new Node(x);
            node.next := null;
            node.prev := tail;

            if tail == null {
                head := node;
            } else {
                node.prev.next := node;
            }

            tail := node;
            spine := spine + [node];
            contents := contents + [x];
            repr := repr + {node};
        }

        method Index(i: int) returns (x: T)
            requires 0 <= i < |contents|
            requires Valid()
            ensures x == contents[i]
        {
            var j := 0;
            var node := head;

            while j < i
                invariant 0 <= j <= i
                invariant i - j < |contents|
                invariant node == spine[j]
            {
                node := node.next;
                j := j + 1;
            }

            x := node.data;
        }
    }
}


module RingBuffer {
    import opened Prelude

    export provides RingBuffer, RingBuffer.Valid, RingBuffer.repr, RingBuffer.contents,
                    RingBuffer.Capacity, RingBuffer.RingBuffer,
                    RingBuffer.PushBack


    class RingBuffer<T(0)> {
        var buf: array<T>
        var start: int
        var end: int

        ghost var contents: seq<T>
        ghost var repr: set<object>

        constructor RingBuffer(len: nat)
            requires len > 0
            ensures Valid() && contents == [] && fresh(repr) && Capacity() == len
        {
            buf := new T[len + 1];
            start := 0;
            end := 0;
            contents := [];
            repr := {buf};
        }


        predicate Valid()
            reads this, repr
            ensures Valid() ==> null !in repr
        {
            && null !in repr
            && this !in repr
            && buf in repr
            && 0 <= start < buf.Length
            && 0 <= end < buf.Length
            && contents == Contents()
        }

        function Contents(): seq<T>
            reads this, repr
            requires
                && null !in repr
                && buf in repr
                && 0 <= start < buf.Length
                && 0 <= end < buf.Length
        {
            if start <= end then
                buf[start..end]
            else
                buf[start..] + buf[..end]
        }

        function Size(): nat
            reads this, repr
            requires Valid()
        {
            if start <= end then
                end - start
            else
                buf.Length - start + end
        }

        function Capacity(): nat
            reads this, repr
            requires Valid()
        {
            buf.Length - 1
        }

        function method {:opaque} Clip(i: int): int
            reads this
            requires buf != null && buf.Length != 0
            ensures 0 <= Clip(i) < buf.Length
            ensures -1 <= i <= buf.Length ==>
                || (i == -1 && Clip(i) == buf.Length - 1)
                || (i < buf.Length && Clip(i) == i)
                || (i == buf.Length && Clip(i) == 0)
        {
            i % buf.Length
        }

        method PushBack(t: T)
            requires Valid() && |contents| < Capacity()
            modifies this, repr
            ensures Valid() && fresh(repr - old(repr)) && contents == old(contents) + [t]
            ensures Capacity() == old(Capacity())
        {
            buf[end] := t;
            end := Clip(end + 1);
            contents := contents + [t];
        }

        method PushFront(t: T)
            requires Valid() && |contents| < Capacity()
            modifies this, repr
            ensures Valid() && contents == [t] + old(contents)
        {
            start := Clip(start - 1);
            buf[start] := t;
            contents := [t] + contents;
        }

        method PopBack() returns (x: T)
            requires Valid() && |contents| > 0
            modifies this, repr
            ensures Valid() && contents + [x] == old(contents)
        {
            end := Clip(end - 1);
            x := buf[end];
            contents := contents[..|contents|-1];
        }

        method PopFront() returns (x: T)
            requires Valid() && |contents| > 0
            modifies this, repr
            ensures Valid() && [x] + contents == old(contents)
        {
            x := buf[start];
            assert x == contents[0];
            start := Clip(start + 1);
            contents := contents[1..];
        }
    }
}


module Vector {
    import Prelude
    import Array

    export provides Vector, Vector.Vector, Vector.Valid, Vector.contents, Vector.repr,
                    Vector.PushBack

    class Vector<T(0)> {
        var buf: array<T>
        var end: int

        ghost var contents: seq<T>
        ghost var repr: set<object>

        constructor Vector()
            ensures Valid() && contents == [] && fresh(repr)
        {
            buf := new T[10];
            end := 0;
            repr := {buf};
            contents := [];
        }

        predicate Valid()
            reads this, repr
            ensures Valid() ==> null !in repr
        {
            && null !in repr
            && this !in repr
            && buf in repr
            && 0 <= end <= buf.Length
            && contents == buf[..end]
        }

        method Resize(n: int)
            requires Valid()
            modifies this, repr
            ensures Valid() && contents == old(contents) && buf.Length >= n
            ensures fresh(repr - old(repr))
        {
            if n <= buf.Length { return; }

            var n' := Prelude.Max(n, 2 * buf.Length);
            var a := new T[n'];
            Array.Copy(a, 0, buf, 0, end);
            buf := a;
            repr := {buf};
        }

        method PushBack(x: T)
            requires Valid()
            modifies this, repr
            ensures Valid() && fresh(repr - old(repr)) && contents == old(contents) + [x]
        {
            Resize(end + 1);
            buf[end] := x;
            end := end + 1;
            contents := contents + [x];
        }

        method PushFront(x: T)
            requires Valid()
            modifies this, repr
            ensures Valid() && contents == [x] + old(contents)
        {
            Insert(0, x);
        }

        method PopFront() returns (x: T)
            requires Valid() && end > 0
            modifies this, repr
            ensures Valid() && [x] + contents == old(contents)
        {
            x := buf[0];
            Remove(0);
        }

        method Insert(i: int, x: T)
            requires Valid() && 0 <= i <= end
            modifies this, repr
            ensures Valid() && end == old(end) + 1
            ensures contents[..i] == old(contents[..i])
            ensures contents[i+1..] == old(contents[i..])
            ensures contents[i] == x
        {
            Resize(end + 1);
            Array.Copy(buf, i + 1, buf, i, end - i);
            buf[i] := x;
            contents := contents[..i] + [x] + contents[i..];
            end := end + 1;
        }

        method PopBack()
            requires Valid() && end > 0
            modifies this, repr
            ensures Valid() && contents == old(contents[..end-1])
        {
            contents := contents[..end-1];
            end := end - 1;
        }

        method Remove(i: int)
            requires Valid() && 0 <= i < end
            modifies this, repr
            ensures Valid() && contents == old(contents[..i] + contents[i+1..])
        {
            Array.Copy(buf, i, buf, i + 1, end - i - 1);
            end := end - 1;
            contents := contents[..i] + contents[i+1..];
        }
    }
}

module Client {

    import Dequeue = DoublyLinkedList

    method Main(n: nat)
    {
        var d := new Dequeue.List<int>.List();
        var i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant d.Valid() && fresh(d.repr)
            invariant |d.contents| == i
            invariant forall j | 0 <= j < i :: d.contents[j] == j
        {
            d.PushBack(i);
            i := i + 1;
        }

    }

}

// RUN: /compile:0 /noCheating:1

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
    class Node<T> {
        var next: Node<T>
        var data: T

        ghost var repr: set<object>
        ghost var contents: seq<Node<T>>

        predicate Valid()
            reads this, repr
        {
            && this in repr
            && null !in repr
            && if next == null then
                && contents == []
              else
                && next in repr
                && next.repr <= repr
                && this !in next.repr
                && contents == [this] + next.contents
                && next.Valid()
        }

        constructor(data: T, next: Node<T>) {
            this.next := next;
            this.data := data;
            repr := {this} + GetRepr(next);
            contents := [this] + GetContents(next);
        }

        static function GetRepr<T>(node: Node<T>): set<object>
            reads node
        {
            if node == null then
                {}
            else
                node.repr
        }

        static function GetContents<T>(node: Node<T>): seq<Node<T>>
            reads node
        {
            if node == null then
                []
            else
                node.contents
        }
    }

    class List<T> {
        var head: Node<T>

        predicate Valid()
            reads this, head, if head != null then head.repr else {}
        {
            head != null ==> head.Valid()
        }
    }
}

module DoublyLinkedList {
    import Prelude

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
        ghost var contents: seq<T>

        static predicate ValidViaNext(
            x: Node<T>,
            repr: set<object>,
            contents: seq<T>,
            tail: Node<T>
            )
            requires null !in repr
            decreases contents
            reads repr
        {
            if contents == [] then
                x == null
            else
                && x in repr
                && contents[0] == x.data
                && (if x.next == null then x == tail
                   else x.next in repr && x.next.prev == x)
                && ValidViaNext(x.next, repr - {x}, contents[1..], tail)

        }

        predicate Valid()
            reads this, repr
        {
            && (head == null <==> tail == null)
            && null !in repr
            && this !in repr
            && (head != null ==> head in repr && head.prev == null)
            && ValidViaNext(head, repr, contents, tail)
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
            contents := [x] + contents;
            repr := repr + {node};
        }

        static lemma ValidViaNextTailInRepr(
            x: Node<T>,
            repr: set<object>,
            contents: seq<T>,
            tail: Node<T>
            )
            requires null !in repr && ValidViaNext(x, repr, contents, tail)
            requires contents != []
            ensures tail in repr
        {}

        static lemma ValidViaNextTailNext(
            x: Node<T>,
            repr: set<object>,
            contents: seq<T>,
            tail: Node<T>
            )
            requires null !in repr && ValidViaNext(x, repr, contents, tail)
            requires contents != []
            ensures tail != null && tail.next == null
        {}

        static twostate lemma ValidViaNextPushBack(
            x: Node<T>,
            repr: set<object>,
            contents: seq<T>,
            tail: Node<T>,
            node: Node<T>
            )
            requires null !in repr && old(ValidViaNext(x, repr, contents, tail))
            requires tail != null && node != null && node !in repr
            requires node.prev == tail && tail.next == node && node.next == null
            requires unchanged(repr - {tail})
            ensures ValidViaNext(x, repr + {node}, contents + [node.data], node)
        {
            var y := x;
            var r := repr;
            var c := contents;
            while |c| > 0
                invariant null !in r
                invariant unchanged(r - {tail})
                invariant old(allocated(y) && allocated(r) && allocated(c))
                invariant old(ValidViaNext(y, r, c, tail))
            {
                r := r - {y};
                y := y.next;
                c := c[1..];
            }

        }


        method PushBack(x: T)
            requires Valid()
            modifies this, repr
            ensures Valid() && contents == old(contents) + [x]
        {
            var node := new Node(x);
            node.next := null;
            node.prev := tail;

            if tail == null {
                head := node;
            } else {
                ValidViaNextTailInRepr(head, repr, contents, tail);
                node.prev.next := node;
            }

            tail := node;
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
            ghost var repr := this.repr;
            ghost var contents := this.contents;

            while j < i
                invariant null !in repr
                invariant 0 <= j <= i
                invariant i - j < |contents|
                invariant contents == old(this.contents[j..])
                invariant ValidViaNext(node, repr, contents, tail)
            {
                repr := repr - {node};
                contents := contents[1..];
                node := node.next;
                j := j + 1;
            }

            x := node.data;
        }
    }
}


module RingBuffer {
    import opened Prelude

    class RingBuffer<T> {
        var buf: array<T>
        var start: int
        var end: int

        ghost var contents: seq<T>

        predicate Valid()
            reads this, buf
        {
            && buf != null
            && buf.Length != 0
            && 0 <= start < buf.Length
            && 0 <= end < buf.Length
            && contents == Contents()
        }

        function Contents(): seq<T>
            reads this, buf
            requires
                && buf != null
                && 0 <= start < buf.Length
                && 0 <= end < buf.Length
        {
            if start <= end then
                buf[start..end]
            else
                buf[start..] + buf[..end]
        }

        function Size(): int
            reads this
            requires buf != null
        {
            if start <= end then
                end - start
            else
                buf.Length - start + end
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

        lemma SizeContents()
            requires Valid()
            ensures Size() == |contents|
        {}

        method PushBack(t: T)
            requires Valid() && Size() < buf.Length - 1
            modifies this, buf
            ensures Valid() && contents == old(contents) + [t]
        {
            buf[end] := t;
            end := Clip(end + 1);
            contents := contents + [t];
        }

        method PushFront(t: T)
            requires Valid() && Size() < buf.Length - 1
            modifies this, buf
            ensures Valid() && contents == [t] + old(contents)
        {
            start := Clip(start - 1);
            buf[start] := t;
            contents := [t] + contents;
        }

        method PopBack() returns (x: T)
            requires Valid() && Size() > 0
            modifies this, buf
            ensures Valid() && contents + [x] == old(contents)
        {
            end := Clip(end - 1);
            x := buf[end];
            contents := contents[..|contents|-1];
        }

        method PopFront() returns (x: T)
            requires Valid() && Size() > 0
            modifies this, buf
            ensures Valid() && [x] + contents == old(contents)
        {
            x := buf[start];
            start := Clip(start + 1);
            contents := contents[1..];
        }
    }
}


module Vector {
    import Prelude
    import Array

    class Vector<T(0)> {
        var buf: array<T>
        var end: int

        ghost var contents: seq<T>

        predicate Valid()
            reads this, buf
        {
            && buf != null
            && 0 <= end <= buf.Length
            && contents == buf[..end]
        }

        method Resize(n: int)
            requires Valid()
            modifies this
            ensures Valid() && contents == old(contents) && buf.Length >= n
            ensures buf == old(buf) || fresh(buf)
        {
            if n <= buf.Length { return; }

            var n' := Prelude.Max(n, 2 * buf.Length);
            var a := new T[n'];
            Array.Copy(a, 0, buf, 0, end);
            buf := a;
        }

        method Add(x: T)
            requires Valid()
            modifies this, buf
            ensures Valid() && contents == old(contents) + [x]
        {
            Resize(end + 1);
            buf[end] := x;
            end := end + 1;
            contents := contents + [x];
        }

        method Insert(i: int, x: T)
            requires Valid() && 0 <= i <= end
            modifies this, buf
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

        method Pop()
            requires Valid() && end > 0
            modifies this, buf
            ensures Valid() && contents == old(contents[..end-1])
        {
            contents := contents[..end-1];
            end := end - 1;
        }

        method Remove(i: int)
            requires Valid() && 0 <= i < end
            modifies this, buf
            ensures Valid() && contents == old(contents[..i] + contents[i+1..])
        {
            Array.Copy(buf, i, buf, i + 1, end - i - 1);
            end := end - 1;
            contents := contents[..i] + contents[i+1..];
        }
    }
}

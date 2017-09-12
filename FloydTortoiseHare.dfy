// RUN: /compile:0 /nologo /noCheating:1 /rlimit:1000000 /proc:*CycleMod*

lemma SetNeq<A>(x: A, s1: set<A>, s2: set<A>)
    requires x in s1 && x !in s2
    ensures s1 != s2
{ }

datatype CycleDetectionResult = NullReachable(n: nat) | Cycle(j: nat, k: nat)

class Node {
    ghost var reachable: set<Node>

    var next: Node

    predicate ValidAux(visited: set<Node>)
        requires this !in visited
        reads this, reachable
        decreases reachable - visited
    {
        && this in reachable
        && (next != null ==>
            && next in reachable
            && next.reachable <= reachable
            && (next !in visited + {this} ==>
                calc {
                    next.reachable - (visited + {this});
                    < { SetNeq(this, reachable - visited, next.reachable - (visited + {this})); }
                    reachable - visited;
                }
                next.ValidAux(visited + {this})))
    }

    predicate Valid()
        reads this, reachable
    {
        ValidAux({})
    }

    predicate ValidToDepth(n: nat)
        reads this, reachable
    {
        && this in reachable
        && (n != 0 && next != null ==>
            && next in reachable
            && next.reachable <= reachable
            && next.ValidToDepth(n - 1))
    }

    function Hop(i: nat): Node
        requires ValidToDepth(i)
        reads reachable
    {
        if i == 0 then
            this
        else if next == null then
            null
        else
            next.Hop(i - 1)
    }

    lemma ValidToDepthDecrease(n: nat)
        requires ValidToDepth(n) && n != 0
        ensures ValidToDepth(n-1)
    {
        if n > 1 && next != null {
            next.ValidToDepthDecrease(n-1);
        }
    }

    lemma ValidToDepthLe(n1: nat, n2: nat)
        requires ValidToDepth(n1) && n2 <= n1
        ensures ValidToDepth(n2)
    {
        if n1 != n2 {
            ValidToDepthDecrease(n1);
        }
    }


    lemma HopExtend(i: nat)
        requires ValidToDepth(i + 1)
        ensures (ValidToDepthDecrease(i + 1); Hop(i) != null ==> Hop(i+1) == Hop(i).next)
    {
        ValidToDepthDecrease(i + 1);
        if i != 0 && next != null {
            next.HopExtend(i - 1);
        }
    }

    lemma HopUnroll(i: nat)
        requires i > 0 && ValidToDepth(i)
        ensures next != null ==> Hop(i) == next.Hop(i-1)
    { }


    lemma HopValidToDepthIncrease(y: Node, n: nat)
        requires ValidToDepth(n) && Hop(n) == y
        requires y != null && y.next != null ==>
            && y.next in y.reachable
            && y.next.reachable <= y.reachable
            && y.next in y.next.reachable
        ensures ValidToDepth(n + 1)
    {
        if n != 0 && next != null {
            next.HopValidToDepthIncrease(y, n - 1);
        }
    }



    lemma ValidToDepthHop(i: nat, j: nat)
        requires ValidToDepth(i)
        requires Hop(i) != null ==> Hop(i).ValidToDepth(j)
        ensures ValidToDepth(i+j)
    {
        if i != 0 && next != null {
            ValidToDepthDecrease(i);
            next.ValidToDepthHop(i-1, j);
        }
    }

    lemma ValidToDepthSplit(i: nat, j: nat)
        requires ValidToDepth(i+j)
        ensures (ValidToDepthLe(i+j, i); Hop(i) != null ==> Hop(i).ValidToDepth(j))
    {
        if i != 0 && next != null {
            ValidToDepthLe(i+j, i);
            next.ValidToDepthSplit(i-1, j);
        }
    }

    lemma LoopValidToAnyDepth(n: nat, goal: nat)
        requires n > 0 && ValidToDepth(n) && Hop(n) == this
        ensures ValidToDepth(goal)
    {
        if goal <= n {
            ValidToDepthLe(n, goal);
        } else {
            LoopValidToAnyDepth(n, goal - n);
            ValidToDepthHop(n, goal - n);

        }
    }

    predicate LastVisitedValid(last_visited: map<Node, nat>)
        requires this !in last_visited && ValidAux(last_visited.Keys) && null !in last_visited
        reads this, reachable, (set x | x in last_visited),
              set x, y | x in last_visited && y in x.reachable :: y
    {
        forall x :: x in last_visited ==>
            && x.ValidToDepth(last_visited[x])
            && x.Hop(last_visited[x]) == this
    }

    lemma LastVisitedExtend(last_visited: map<Node, nat>) returns (last_visited': map<Node, nat>)
        requires next != null && next !in last_visited && null !in last_visited && this != next
        requires this !in last_visited && ValidAux(last_visited.Keys)
        requires LastVisitedValid(last_visited)
        ensures last_visited' ==
            (map x | x in last_visited :: last_visited[x] + 1)[this := 1]
        ensures next.ValidAux(last_visited'.Keys)
        ensures next.LastVisitedValid(last_visited')
        ensures last_visited'.Keys == last_visited.Keys + {this}
    {
        var inc_last_visited := map x | x in last_visited :: last_visited[x] + 1;
        last_visited' := inc_last_visited[this := 1];

        forall x | x in last_visited'
            ensures x.ValidToDepth(last_visited'[x]) && x.Hop(last_visited'[x]) == next
        {
            var i := last_visited'[x];
            if x == this {
                assert x.Hop(1) == next;
                assert x.ValidToDepth(i) && x.Hop(i) == next;
            } else {
                assert x in inc_last_visited;
                assert x.ValidToDepth(last_visited[x]) && x.Hop(last_visited[x]) == this;
                x.HopValidToDepthIncrease(this, last_visited[x]);
                x.HopExtend(last_visited[x]);
                assert x.ValidToDepth(last_visited'[x]) && x.Hop(last_visited'[x]) == next;
            }
        }
        assert last_visited'.Keys == last_visited.Keys + {this};
    }

    lemma LastVisitedLoop(last_visited: map<Node, nat>) returns (k: nat)
        requires this !in last_visited && ValidAux(last_visited.Keys) && null !in last_visited
        requires LastVisitedValid(last_visited)
        requires next != null && next in last_visited
        ensures k > 0 && next.ValidToDepth(k) && next.Hop(k) == next
    {
        k := last_visited[next];
        assert next.Hop(k) == this;
        next.HopValidToDepthIncrease(this, k);
        next.HopExtend(k);
        k := k + 1;
        assert next.Hop(k) == next;
    }

    lemma ValidAuxDepth(n: nat, last_visited: map<Node, nat>)
        requires this !in last_visited && ValidAux(last_visited.Keys) && null !in last_visited
        requires LastVisitedValid(last_visited)
        ensures ValidToDepth(n)
        decreases n
    {
        if n != 0 && next != null {
            if next == this {
                ValidAuxDepth(n-1, last_visited);
            } else if next in last_visited {
                // there is a loop from next to this, so it's valid to any depth
                var k := LastVisitedLoop(last_visited);
                next.LoopValidToAnyDepth(k, n - 1);
            } else {
                var last_visited': map<Node,nat> := LastVisitedExtend(last_visited);
                next.ValidAuxDepth(n-1, last_visited');
            }
        }
    }

    function CycleDetectionResultMetric(c: CycleDetectionResult): nat
    {
        match c
            case NullReachable(n) => n
            case Cycle(j, k) => j + k
    }

    predicate CycleDetectionResultValid(c: CycleDetectionResult)
        reads this, reachable,
            (set j: nat | ValidToDepth(j) && Hop(j) != null :: Hop(j)),
            (set j: nat, x | ValidToDepth(j) && Hop(j) != null && x in Hop(j).reachable :: x)

    {
        match c
            case NullReachable(n) => ValidToDepth(n) && Hop(n) == null
            case Cycle(j, k) =>
                && k > 0
                && ValidToDepth(j)
                && Hop(j) != null
                && Hop(j).ValidToDepth(k)
                && Hop(j).Hop(k) == Hop(j)
    }

    function CycleDetectionResultNext(c: CycleDetectionResult): CycleDetectionResult
    {
        match c
            case NullReachable(n) =>
                if n > 1 then
                    NullReachable(n - 1)
                else
                    c

            case Cycle(j, k) =>
                if j > 0 then
                    Cycle(j - 1, k)
                else
                    c
    }

    lemma CycleDetectionResultValidNext(c: CycleDetectionResult)
        requires CycleDetectionResultValid(c)
        ensures next != null ==> next.CycleDetectionResultValid(CycleDetectionResultNext(c))
    {
        match c
            case NullReachable(n) => {
                if n > 1 {
                    HopUnroll(n);
                } else {
                    if n == 0 {
                    } else {
                        assert n == 1;
                        assert Hop(1) == null;
                    }
                }
            }
            case Cycle(j, k) => {
                if j > 0 {
                } else {
                    assert j == 0;
                    assert Hop(0) == this;
                    assert
                        && k > 0
                        && ValidToDepth(k)
                        && Hop(k) == this;

                    LoopValidToAnyDepth(k, k + 1);
                    HopUnroll(k + 1);
                    next.HopExtend(k - 1);
                    assert next.Hop(k) == next;
                }
            }
    }

    static lemma CycleModHelper1(n: int, k: nat)
        requires k > 0 && 0 <= n < k
        ensures n == n % k
    {
        assert n == (n / k) * k + n % k;
        assert n / k == 0;
        assert n == n % k;
    }

    static lemma CycleModHelper3(a: int, k: int)
        requires k > 0
        ensures 1 + a / k == (a + k) / k
    {
        assert a == (a / k) * k + a % k;
        assert a + k == ((a + k) / k) * k + (a + k) % k;
        assert (a + k) % k == a % k;

        calc {
            k * (1 + a / k);
            k + (a / k) * k;
            k + a - a % k;
        }
    }


    static lemma CycleModHelper2(n: int, k: int)
        requires k > 0 && k <= n
        ensures (n - k) % k == n % k
    {
        assert (n - k) == ((n - k) / k) * k + (n - k) % k;
        assert n == (1 + (n - k) / k) * k + (n - k) % k;
        assert n == (k / k + (n - k) / k) * k + (n - k) % k;
        CycleModHelper3(n - k, k);
        assert n == ((k + n - k) / k) * k + (n - k) % k;
        assert n == (n / k) * k + (n - k) % k;
        assert n == (n / k) * k + n % k;

    }


    lemma CycleMod(j: nat, k: nat, n: nat)
        requires CycleDetectionResultValid(Cycle(j, k))
        requires n >= j
        decreases j, n
        ensures ValidToDepth(n) && ValidToDepth(j + (n - j) % k)
        ensures Hop(n) == Hop(j + (n - j) % k)
    {
        if j > 0 {
            CycleDetectionResultValidNext(Cycle(j, k));
            next.CycleMod(j - 1, k, n - 1);
        } else {
            assert j == 0;
            assert Hop(0) == this;
            assert Hop(k) == this;
            assert ValidToDepth(k);
            LoopValidToAnyDepth(k, n);
            LoopValidToAnyDepth(k, n % k);
            if n < k {
                CycleModHelper1(n, k);
                assert Hop(n) == Hop(n%k);
            } else {
                CycleMod(0, k, n - k);
            }
        }
    }
/*
    lemma CycleTtl(j: nat, k: nat) returns (ttl: nat)
        requires CycleDetectionResultValid(Cycle(j, k))
        ensures ValidToDepth(ttl) && ValidToDepth(2 * ttl) && Hop(ttl) == Hop(2 * ttl)
    {
        var i := j % k;
        ttl := j + k - i;
    }
*/
    lemma FindCycleAux(last_visited: map<Node, nat>) returns (c: CycleDetectionResult)
        requires this !in last_visited && ValidAux(last_visited.Keys) && null !in last_visited
        requires forall x :: x in last_visited ==>
            && x.ValidToDepth(last_visited[x])
            && x.Hop(last_visited[x]) == this

        ensures CycleDetectionResultValid(c)

        decreases reachable - last_visited.Keys
    {
        if next == null {
            c := NullReachable(1);
            assert ValidToDepth(1) && Hop(1) == null;
        } else if next == this {
            assert
                && ValidToDepth(0)
                && Hop(1) == next == this != null
                && Hop(0).ValidToDepth(1)
                && Hop(0).Hop(1) == Hop(0);
            c := Cycle(0, 1);
        } else if next in last_visited {
            var k := LastVisitedLoop(last_visited);

            c := Cycle(1, k);

            assert
                && c.k > 0
                && ValidToDepth(c.j)
                && Hop(c.j) != null
                && Hop(c.j).ValidToDepth(c.k)
                && Hop(c.j).Hop(c.k) == Hop(c.j);

        } else {
            var last_visited': map<Node,nat> := LastVisitedExtend(last_visited);

            c := next.FindCycleAux(last_visited');

            match c
                case NullReachable(n) =>
                    assert ValidToDepth(n+1) && Hop(n+1) == null;
                    c := NullReachable(n+1);
                case Cycle(j, k) =>
                    assert
                        && k > 0
                        && next.ValidToDepth(j)
                        && next.Hop(j) != null
                        && next.Hop(j).ValidToDepth(k)
                        && next.Hop(j).Hop(k) == next.Hop(j);

                    assert
                        && ValidToDepth(j+1)
                        && Hop(j+1) != null
                        && Hop(j+1).ValidToDepth(k)
                        && Hop(j+1).Hop(k) == Hop(j+1);

                    c := Cycle(j+1, k);
        }
    }

    lemma FindCycle() returns (c: CycleDetectionResult)
        requires ValidAux({})
        ensures CycleDetectionResultValid(c)
    {
        var m := map[];
        assert m.Keys == {};
        c := FindCycleAux(m);
    }

    lemma ValidToAnyDepth(n: nat)
        requires Valid()
        ensures ValidToDepth(n)
    {
        var m := map[];
        assert m.Keys == {};
        ValidAuxDepth(n, m);
    }
}




method TortoiseHare(n: Node) returns (cycle: bool, ghost i: nat, ghost j: nat)
    requires n != null ==> n.Valid()
    ensures cycle ==>
        && j > 0
        && n != null
        && n.ValidToDepth(i)
        && var head := n.Hop(i);
        && head != null
        && head.ValidToDepth(j)
        && head.Hop(j) == head

/*    ensures !cycle && n != null ==>
        forall k: nat, l: nat :: k != l ==>
            (n.ValidToAnyDepth(k); n.ValidToAnyDepth(l);
            n.Hop(k) != n.Hop(l) || n.Hop(k) == n.Hop(l) == null) */

{
    if n == null { return false, 0, 0; }

    var tortoise := n;
    var hare := n.next;

    ghost var tortoise_i := 0;
    ghost var hare_i := 1;

    ghost var c := n.FindCycle();

    tortoise.ValidToAnyDepth(1);
    assert tortoise.Hop(1) == hare;

    while hare != null && hare != tortoise
        invariant tortoise != null
        invariant n.ValidToDepth(tortoise_i) && n.Hop(tortoise_i) == tortoise
        invariant tortoise.ValidToDepth(hare_i) && tortoise.Hop(hare_i) == hare
        invariant tortoise_i <= n.CycleDetectionResultMetric(c)
        decreases n.CycleDetectionResultMetric(c) - tortoise_i

        /*invariant forall k: nat, l: nat :: k != l ==>
            (n.ValidToAnyDepth(k); n.ValidToAnyDepth(l);
            n.Hop(k) != n.Hop(l) || n.Hop(k) == n.Hop(l) == null)*/
    {
        if hare.next == null { return false, 0, 0; }

        n.ValidToAnyDepth(tortoise_i+1);
        n.HopExtend(tortoise_i);

        n.ValidToAnyDepth(tortoise_i + hare_i + 1);
        n.ValidToDepthSplit(tortoise_i, hare_i + 1);

        tortoise.HopUnroll(hare_i);
        tortoise.next.HopExtend(hare_i - 1);

        tortoise := tortoise.next;
        hare := hare.next.next;

        n.ValidToAnyDepth((tortoise_i + 1) + (hare_i + 1));
        n.ValidToDepthSplit(tortoise_i + 1, hare_i + 1);

        tortoise.HopExtend(hare_i);

        match c {
            case NullReachable(n) => {
            }
            case Cycle(j, k) => {
                if tortoise_i <= j {
                    assert tortoise_i + 1 <= n.CycleDetectionResultMetric(c);
                } else {
                    var i: nat := tortoise_i - j;
                    assert tortoise_i + 1 <= n.CycleDetectionResultMetric(c);
                }
            }
        }


        tortoise_i := tortoise_i + 1;
        hare_i := hare_i + 1;
    }

    if hare == null { return false, 0, 0; }

    return true, tortoise_i, hare_i;
}

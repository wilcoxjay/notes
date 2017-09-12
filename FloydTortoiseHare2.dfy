class Node {
    var next: Node

    ghost var reachable: set<Node>

    predicate Valid(n: nat)
        reads this, reachable
    {
        && this in reachable
        && (n != 0 && next != null ==>
            && next in reachable
            && next.reachable <= reachable
            && next.Valid(n - 1))
    }
}

function Hop(n: Node, i: nat): Node
    requires n != null ==> n.Valid(i)
    reads if n != null then n.reachable else {}
{
    if i == 0 then
        n
    else if n == null then
        null
    else
        Hop(n.next, i - 1)
}

method TortoiseHare(n: Node) returns (cycle: bool)
    decreases *
{
    if n == null { return false; }

    var tortoise := n;
    var hare := n.next;

    while hare != null && hare != tortoise
        decreases *
        invariant tortoise != null
    {
        if hare.next == null { return false; }

        hare := hare.next.next;
        tortoise := tortoise.next;
    }

    if hare == null { return false; }

    return true;
}

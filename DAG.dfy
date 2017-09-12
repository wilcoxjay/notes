// RUN: /compile:0

class Node {
    var children: set<Node>
    ghost var repr: set<object>
    
    predicate Valid()
        reads this, repr
    {
        && this in repr
        && null !in repr
        && forall x | x in children :: 
            && x in repr
            && x.repr <= repr
            && this !in x.repr
            && x.Valid()
    }

    predicate Reachable(c: Node)
        reads this, repr
        requires Valid()
    {
        || c == this
        || exists x | x in children :: x.Reachable(c)
    }

    constructor(children: set<Node>) 
        requires forall c | c in children :: c != null && c.Valid()
        ensures Valid()
    {
        this.children := children;
        repr := {};
        new;
        ghost var R := {this};
        ghost var S := children;
        while S != {}
            decreases S
            invariant this in R
            invariant null !in R
            invariant forall x | x in children && x !in S :: x in R && x.repr <= R
        {
            var x: Node :| x in S;
            R := R + x.repr;
            S := S - {x};
        }
        repr := R;
    }
}

class TopoSort {
    var result: seq<Node>

    method Visit(n: Node)
        requires n != null && n.Valid() 
        requires this !in n.repr 
        requires forall x | x in result :: 
            && x != null 
            && this !in x.repr
            && x.Valid()
            && (forall y | x.Reachable(y) :: y in result)
        decreases n.repr
        modifies this
        ensures forall x | x in old(result) :: x in result
        ensures forall x | n.Reachable(x) :: x in result
        ensures forall x | x in result :: 
            && x != null 
            && this !in x.repr
            && x.Valid()
            && (forall y | x.Reachable(y) :: y in result)
    {
        if n in result { return; }
        var S := n.children;
        while S != {}
            decreases S
            invariant forall x | x in old(result) :: x in result
            invariant forall x | x in n.children :: x in S || x in result
            invariant forall x | x in result :: 
                && x != null 
                && this !in x.repr
                && x.Valid()
                && (forall y | x.Reachable(y) :: y in result)
        {
            var x :| x in S;
            Visit(x);
            S := S - {x};
        }
        result := [n] + result;
    }
}

method TopoSort(nodes: set<Node>) returns (s: seq<Node>)
    requires forall n | n in nodes :: n != null && n.Valid()
    ensures forall n | n in nodes :: forall x | n.Reachable(x) :: x in s
{
    var state := new TopoSort;
    state.result := [];
    
    var S := nodes;
    while S != {}
        decreases S
        invariant forall n' | n' in nodes :: state !in n'.repr;
        invariant forall n: Node | n in nodes && n !in S :: forall x | n.Reachable(x) :: x in state.result
        invariant forall x | x in state.result :: 
            && x != null 
            && state !in x.repr
            && x.Valid()
            && (forall y | x.Reachable(y) :: y in state.result)
    {
        var n :| n in S;
        state.Visit(n);
        S := S - {n};
    }

    return state.result;
}

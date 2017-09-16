// RUN: /compile:0 /rlimit:2000000

datatype Graph<A> = Graph(nodes: set<A>, edges: set<(A,A)>)

predicate ValidGraph<A>(g: Graph<A>)
{
    var Graph(nodes, edges) := g;
    forall u, v | (u, v) in edges :: u in nodes && v in nodes
}

type Path<A> = seq<A>

predicate ValidPath<A>(g: Graph<A>, p: Path<A>)
{
    && |p| > 0
    && p[0] in g.nodes
    && forall i | 0 <= i < |p|-1 :: (p[i], p[i+1]) in g.edges
}

function last<A>(s: seq<A>): A
    requires |s| > 0
{
    s[|s| - 1]
}

predicate ValidDAG<A>(g: Graph<A>)
{
    && ValidGraph(g)
    && forall p | ValidPath(g, p) :: |p| > 1 ==> p[0] != last(p)
}

predicate DiamondNode(i: int)
{
    0 <= i < 4
}

function DiamondDAG(): Graph<int>
{
    Graph(set i {:nowarn} | 0 <= i < 4,
          set i, j |
              && 0 <= i < 4
              && 0 <= j < 4
              && (|| (i == 0 && j == 1)
                 || (i == 0 && j == 2)
                 || (i == 1 && j == 3)
                 || (i == 2 && j == 3))
              :: (i, j))
}

lemma lemma_DiamondDAGValid()
    ensures ValidDAG(DiamondDAG())
{
    var g := DiamondDAG();
    forall p | ValidPath(g, p) && |p| > 1
        ensures p[0] != last(p)
    {
        assert (p[0], p[1]) in g.edges;
        assert |p| > 2 ==> (p[1], p[2]) in g.edges;
        assert |p| > 3 ==> (p[2], p[3]) in g.edges;
    }
}

class Node {
    var children: set<Node>
    ghost var repr: set<object>

    predicate LocallyValid()
        reads this, repr
    {
        && this in repr
        && null !in repr
        && forall x | x in children ::
            && x in repr
            && x.repr <= repr
    }

    predicate DAGValid()
        reads this, repr
    {
        && LocallyValid()
        && forall x | x in children ::
            && this !in x.repr
            && x.DAGValid()
    }

    predicate LocallyRespectsGraph(g: Graph<Node>)
        reads this
    {
        && this in g.nodes
        && children == set p | p in g.edges && p.0 == this :: p.1
    }

    predicate PathTo(c: Node)
        reads this, repr
        requires DAGValid()
    {
        || c == this
        || exists x | x in children :: x.PathTo(c)
    }

    constructor(children: set<Node>) 
        requires forall c | c in children :: c != null && c.DAGValid()
        ensures DAGValid()
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

predicate GraphGloballyReflected(g: Graph<Node>)
    reads g.nodes
{
    && null !in g.nodes
    && forall n | n in g.nodes :: n.LocallyRespectsGraph(g)
}


lemma lemma_PathToPathHelper(g: Graph<Node>, x: Node, y: Node) returns (p: Path<Node>)
    requires ValidGraph(g) && GraphGloballyReflected(g)
    requires x in g.nodes && x.DAGValid()
    requires x.PathTo(y)
    ensures ValidPath(g, p) && p[0] == x && last(p) == y
    decreases x.repr
{
    if x == y {
        p := [x];
    } else {
        var c :| c in x.children && c.PathTo(y);
        var q := lemma_PathToPathHelper(g, c, y);
        p := [x] + q;
    }
}

lemma lemma_PathToPath(g: Graph<Node>)
    requires ValidGraph(g) && GraphGloballyReflected(g)
    requires forall x | x in g.nodes :: x.DAGValid()
    ensures forall x, y | x in g.nodes && y in g.nodes && x.PathTo(y) ::
        exists p :: ValidPath(g, p) && p[0] == x && last(p) == y
{
    forall x, y | x in g.nodes && y in g.nodes && x.PathTo(y)
        ensures exists p :: ValidPath(g, p) && |p| > 0 && p[0] == x && last(p) == y
    {
        var p := lemma_PathToPathHelper(g, x, y);
    }
}

lemma lemma_PathPathToHelper(g: Graph<Node>, p: Path<Node>)
    requires ValidGraph(g) && GraphGloballyReflected(g)
    requires ValidPath(g, p)
    requires forall x | x in g.nodes :: x.DAGValid()
    ensures p[0].PathTo(last(p))
{
    if |p| != 1 {
        lemma_PathPathToHelper(g, p[1..]);
    }
}


class TopoSort {
    var result: seq<Node>

    method Visit(n: Node)
        requires n != null && n.DAGValid()
        requires this !in n.repr 
        requires forall x | x in result :: 
            && x != null 
            && this !in x.repr
            && x.DAGValid()
            && (forall y | x.PathTo(y) :: y in result)
        requires forall i, j | 0 <= i < j < |result| ::
            result[j] in result && !result[j].PathTo(result[i])
        decreases n.repr
        modifies this
        ensures forall x | x in old(result) :: x in result
        ensures forall x | n.PathTo(x) :: x in result
        ensures forall x | x in result :: 
            && x != null 
            && this !in x.repr
            && x.DAGValid()
            && (forall y | x.PathTo(y) :: y in result)
        ensures forall i, j | 0 <= i < j < |result| ::
            result[j] in result && !result[j].PathTo(result[i])
        ensures forall x | x in result :: x in old(result) || n.PathTo(x)
    {
        if n in result { return; }
        assert n !in result;
        var S := n.children;
        while S != {}
            decreases S
            invariant n !in result
            invariant forall x | x in old(result) :: x in result
            invariant forall x | x in n.children :: x in S || x in result
            invariant forall x | x in result :: 
                && x != null 
                && this !in x.repr
                && x.DAGValid()
                && (forall y | x.PathTo(y) :: y in result)
            invariant forall i, j | 0 <= i < j < |result| ::
                result[j] in result && !result[j].PathTo(result[i])
            invariant forall x | x in result :: x in old(result) || n.PathTo(x)
        {
            var x :| x in S;
            Visit(x);
            S := S - {x};
        }
        result := [n] + result;
    }
}

method TopoSort(roots: set<Node>) returns (s: seq<Node>)
    requires forall n | n in roots :: n != null && n.DAGValid()
    ensures forall n | n in roots :: forall x | n.PathTo(x) :: x in s
    ensures forall n | n in s :: n != null && n.DAGValid()
    ensures forall i, j | 0 <= i < j < |s| :: s[j] in s && !s[j].PathTo(s[i])
{
    var state := new TopoSort;
    state.result := [];
    
    var S := roots;
    while S != {}
        decreases S
        invariant forall n' | n' in roots :: state !in n'.repr;
        invariant forall n: Node | n in roots && n !in S :: forall x | n.PathTo(x) :: x in state.result
        invariant forall x | x in state.result :: 
            && x != null 
            && state !in x.repr
            && x.DAGValid()
            && (forall y | x.PathTo(y) :: y in state.result)
        invariant forall i, j | 0 <= i < j < |state.result| ::
            state.result[j] in state.result &&
            !state.result[j].PathTo(state.result[i])
    {
        var n :| n in S;
        state.Visit(n);
        S := S - {n};
    }

    s := state.result;
}

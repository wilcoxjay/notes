datatype RoseTree<A> = RoseTree(data: A, children: seq<RoseTree<A>>)

function RoseTreeSize<A>(r: RoseTree<A>): nat
{
    1 + RoseTreeListSize(r.children)
}

function RoseTreeListSize<A>(l: seq<RoseTree<A>>): nat
{
    if l == [] then
        0
    else
        1 + RoseTreeSize(l[0]) + RoseTreeListSize(l[1..])
}

function method ExtractChild<A>(r: RoseTree<A>): RoseTree<A>
{
    if |r.children| == 1 then
        r.children[0]
    else r
}

predicate FilterSafe<A>(f: set<A>, r: RoseTree<A>)
{
    && (r.data in f ==> |r.children| == 1)
    && FilterListSafe(f, r.children)
}

predicate FilterListSafe<A>(f: set<A>, l: seq<RoseTree<A>>)
{
    l != [] ==>
        && FilterSafe(f, l[0])
        && FilterListSafe(f, l[1..])
}

lemma FilterSafe_ExtractChild<A>(f: set<A>, r: RoseTree<A>)
    requires FilterSafe(f, r)
    ensures FilterSafe(f, ExtractChild(r))
{}

lemma FilterSafe_RoseTreeSize_ExtractChild<A>(f: set<A>, r: RoseTree<A>)
    requires FilterSafe(f, r) && r.data in f
    ensures RoseTreeSize(ExtractChild(r)) < RoseTreeSize(r)
{}

function method FilterTree<A>(f: set<A>, r: RoseTree<A>): RoseTree<A>
    requires FilterSafe(f, r)
    decreases RoseTreeSize(r)
{
    if r.data in f then
        var r' := ExtractChild(r);
        FilterSafe_ExtractChild(f, r);
        FilterSafe_RoseTreeSize_ExtractChild(f, r);
        FilterTree(f, r')
    else
        RoseTree(r.data, FilterTreeList(f, r.children))
}

function method FilterTreeList<A>(f: set<A>, l: seq<RoseTree<A>>): seq<RoseTree<A>>
    requires FilterListSafe(f, l)
    decreases RoseTreeListSize(l)
{
    if l == [] then
        []
    else
        [FilterTree(f, l[0])] + FilterTreeList(f, l[1..])
}

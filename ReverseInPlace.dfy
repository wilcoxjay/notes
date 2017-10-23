// RUN: /compile:0 /rlimit:500000 /noCheating:1 /proc:*Destructive*

class Node {
    var next: Node
    ghost var repr: set<object>
    ghost var contents: seq<Node>

    predicate {:opaque} LocallyValid()
        reads this, repr
    {
        && this in repr
        && null !in repr
        && |contents| > 0
        && contents[0] == this
        && (next != null ==>
            && next in repr
            && next.repr <= repr
            && this !in next.repr
            && |next.contents| > 0
            && next.contents[0] == next
            && contents[1..] == next.contents)
        && (next == null ==> |contents| == 1)
    }

    predicate {:opaque} Valid()
        reads this, repr
        decreases repr
    {
        reveal LocallyValid();
        && LocallyValid()
        && (next != null ==> next.Valid())
    }

    method SetNext(next: Node)
        requires next != null ==> next.Valid() && this !in next.repr
        modifies this
        ensures Valid()
        ensures repr == {this} + Node.GetRepr(next)
        ensures contents == [this] + Node.GetContents(next)
    {
        reveal Valid();
        this.next := next;
        this.repr := {this} + Node.GetRepr(next);
        this.contents := [this] + Node.GetContents(next);
    }

    static function GetRepr(n: Node): set<object>
        reads n
    {
        if n == null then
            {}
        else
            n.repr
    }

    static function GetContents(n: Node): seq<Node>
        reads n
    {
        if n == null then
            []
        else
            n.contents
    }

    constructor(next: Node)
        requires next != null ==> next.Valid()
        ensures Valid()
    {
        new;
        SetNext(next);
    }

    lemma lemma_LocallyValid()
        requires Valid()
        ensures LocallyValid()
    {
        reveal Valid();
    }

    twostate lemma twostate_lemma_RevealLocallyValid()
        requires old(LocallyValid())

        ensures old(
            && this in repr
            && null !in repr
            && |contents| > 0
            && contents[0] == this
            && (next != null ==>
                && next in repr
                && next.repr <= repr
                && this !in next.repr
                && |next.contents| > 0
                && next.contents[0] == next
                && contents[1..] == next.contents)
            && (next == null ==> |contents| == 1))
    {
        reveal LocallyValid();
    }


    lemma lemma_EstablishLocallyValid()
        requires
            && this in repr
            && null !in repr
            && |contents| > 0
            && contents[0] == this
            && (next != null ==>
                && next in repr
                && next.repr <= repr
                && this !in next.repr
                && |next.contents| > 0
                && next.contents[0] == next
                && contents[1..] == next.contents)
            && (next == null ==> |contents| == 1)

        ensures LocallyValid()
    {
        reveal LocallyValid();

    }

    lemma lemma_ThisInRepr()
        requires LocallyValid()
        ensures this in repr
    {
        reveal LocallyValid();
    }

    twostate lemma twostate_lemma_ThisInRepr()
        requires old(LocallyValid())
        ensures old(this in repr)
    {
        reveal LocallyValid();
    }

    lemma lemma_NullNotInRepr()
        requires LocallyValid()
        ensures null !in repr
    {
        reveal LocallyValid();
    }

    twostate lemma twostate_lemma_NullNotInRepr()
        requires old(LocallyValid())
        ensures old(null !in repr)
    {
        reveal LocallyValid();
    }

    lemma lemma_NextRepr()
        requires LocallyValid()
        ensures this in repr
        ensures next != null ==> this !in next.repr && next.repr <= repr
    {
        reveal LocallyValid();
    }

    lemma lemma_NextValid()
        requires Valid()
        ensures next != null ==> next.Valid()
    {
        reveal Valid();
    }

    lemma lemma_ContentsInRepr()
        requires Valid()
        ensures forall x {:trigger x in contents} | x in contents :: x in repr
        decreases repr
    {
        reveal Valid();
        if next != null {
            next.lemma_ContentsInRepr();
            forall x | x in contents
                ensures x in repr
            {
                if x != this {
                    assert x in next.contents;
                }
            }
        }
    }

    lemma lemma_ContentsNonNull()
        requires Valid()
        ensures null !in contents
    {
        reveal LocallyValid();
        lemma_LocallyValid();
        lemma_ContentsInRepr();
    }

    lemma lemma_ContentsReprsSubsetRepr()
        requires Valid()
        ensures forall x: Node | x in contents :: x != null && x.repr <= repr
        decreases repr
    {
        reveal Valid();
        if next != null {
            next.lemma_ContentsReprsSubsetRepr();
            forall x: Node | x in contents
                ensures x != null && x.repr <= repr
            {
                assert x != null && x.repr <= repr;
            }
        }
    }

    lemma lemma_ValidSplit()
        requires Valid()
        ensures forall x | x in contents :: x != null && x.LocallyValid()
        decreases repr
    {
        reveal Valid();
        if next != null {
            next.lemma_ValidSplit();
            forall x: Node | x in contents
                ensures x != null && x.LocallyValid()
            {
                assert x != null && x.LocallyValid();
            }
        }
    }

    lemma lemma_ValidCombine()
        requires LocallyValid()
        requires forall x | x in contents :: x != null && x.LocallyValid()
        ensures Valid()
        decreases repr
    {
        reveal Valid(); reveal LocallyValid();
        if next != null {
            assert next in contents;
            forall x | x in next.contents
                ensures x != null && x.LocallyValid()
            {
                assert x in contents;
            }
            next.lemma_ValidCombine();
        }
    }
}

function {:opaque} ReverseSeq<A>(s: seq<A>): seq<A>
{
    if s == [] then
        []
    else
        ReverseSeq(s[1..]) + [s[0]]
}

lemma lemma_ReverseSeqEmpty<A>()
    ensures ReverseSeq<A>([]) == []
{
    reveal ReverseSeq();
}

lemma lemma_ReverseSeqCons<A>(x: A, l: seq<A>)
    ensures ReverseSeq([x] + l) == ReverseSeq(l) + [x]
{
    reveal ReverseSeq();
}

method ReverseNode(n: Node) returns (ans: Node)
    requires n != null ==> n.Valid()
    modifies Node.GetRepr(n)
    ensures ans == null <==> n == null
    ensures ans != null ==>
        && ans.Valid()
        && ans.contents == ReverseSeq(old(n.contents))
{
    if n == null { return null; }
    var temp := n;
    ans := null;

    ghost var S := n.repr;
    ghost var C := n.contents;

    while temp != null
        decreases Node.GetRepr(temp)
        invariant ans != null || temp != null
        invariant ans != null ==> ans.Valid() && ans.repr <= S
        invariant temp != null ==> temp.Valid() && temp.repr <= S
        invariant ans != null && temp != null ==> ans.repr !! temp.repr
        invariant ReverseSeq(Node.GetContents(temp)) + Node.GetContents(ans) == ReverseSeq(C)

        modifies S
    {
        calc {
            ReverseSeq(Node.GetContents(temp)) + Node.GetContents(ans);
            == { reveal temp.Valid();
                 assert Node.GetContents(temp) == [temp] + Node.GetContents(temp.next); }
            ReverseSeq([temp] + Node.GetContents(temp.next)) + Node.GetContents(ans);
            == { lemma_ReverseSeqCons(temp, Node.GetContents(temp.next)); }
            ReverseSeq(Node.GetContents(temp.next)) + [temp] + Node.GetContents(ans);
            ==
            ReverseSeq(Node.GetContents(temp.next)) + ([temp] + Node.GetContents(ans));
        }

        var t := temp.next;
        reveal temp.LocallyValid();
        temp.lemma_LocallyValid();
        temp.lemma_NextValid();
        temp.SetNext(ans);
        ans := temp;
        temp := t;
    }

    lemma_ReverseSeqEmpty<Node>();
}

method DestructiveAppend(n1: Node, n2: Node) returns (n: Node)
    requires n1 != null ==> n1.Valid()
    requires n2 != null ==> n2.Valid()
    requires n1 != null && n2 != null ==> n1.repr !! n2.repr
    modifies Node.GetRepr(n1)
    ensures n != null ==> n.Valid()
    // ensures Node.GetContents(n) == old(Node.GetContents(n1)) + old(Node.GetContents(n2))
{
    if n1 == null { return n2; }
    n := n1;

    var temp := n1;
    ghost var prefix: seq<Node> := [];
    while temp.next != null
        decreases temp.repr
        modifies {}
        invariant temp != null && temp.Valid()
        invariant temp.repr <= n1.repr
        //invariant prefix + temp.contents == old(n1.contents)
    {
        temp.lemma_NextValid();
        temp.lemma_LocallyValid();
        temp.lemma_NextRepr();

        prefix := prefix + [temp];
        temp := temp.next;
    }

    temp.lemma_LocallyValid();
    temp.lemma_ThisInRepr();

    n1.lemma_ValidSplit();

    if n2 != null {
        n2.lemma_LocallyValid();
        n2.lemma_ValidSplit();
    }

    forall x | x in n1.contents
        ensures x != null && x in old(n1.repr)
    {
        n1.lemma_ContentsInRepr();
        n1.lemma_LocallyValid();
        n1.lemma_NullNotInRepr();
    }

    assert n1 in n1.contents by {
        n1.lemma_LocallyValid();
        reveal n1.LocallyValid();
    }

    assert n2 !in n1.contents by {
        n1.lemma_ContentsInRepr();
        if n2 != null {
            n2.lemma_LocallyValid();
            n2.lemma_ThisInRepr();
        }
    }

    ghost var C := n1.contents;

    forall x | x in n1.contents
    {
        x.repr := x.repr + Node.GetRepr(n2);
    }

    forall x | x in n1.contents
    {
        x.contents := x.contents + Node.GetContents(n2);
    }

    temp.next := n2;

    assert n1 in n1.contents;

    forall x | x in n1.contents
        ensures x != null && x.LocallyValid()
    {
        assert x in C || x in Node.GetContents(n2);
        if x in C {
            assert x.LocallyValid() by {
                if n2 != null {
                    n2.lemma_LocallyValid();
                    reveal n2.LocallyValid();
                }

                x.twostate_lemma_RevealLocallyValid();

                if x == temp {
                    x.lemma_EstablishLocallyValid();
                } else {
                    assert x.next == old(x.next);
                    assert x in old(n1.repr);
                    if x.next == null {
                        assert |x.contents| == 1;
                    } else {
                        assert x.next in x.repr;
                        assert x.next.repr <= x.repr;
                        assert x !in x.next.repr;
                        assert |x.next.contents| > 0;
                        assert x.next.contents[0] == x.next;
                        assert x.contents[1..] == x.next.contents;
            
                    }
                    x.lemma_EstablishLocallyValid();
                }
            }
        } else {
        assume false;

            assert x in Node.GetContents(n2);
            assert n2 != null;
            n2.lemma_ContentsNonNull();
            n2.lemma_ContentsInRepr();

            x.twostate_lemma_RevealLocallyValid();

            assert x !in old(n1.repr);
            assert x.repr == old(x.repr);
            assert n2.repr == old(n2.repr);
            n2.lemma_ContentsReprsSubsetRepr();
            assert old(x.repr) <= n2.repr;
            assert x.next == old(x.next);
            assert old(x.next != null ==> x.next in x.repr);
            n1.twostate_lemma_NullNotInRepr();
            assert null !in old(n1.repr);
            assert x in n2.repr;
            assert x.repr !! old(n1.repr);
            assert x.next !in old(n1.repr);

            x.lemma_EstablishLocallyValid();
        }
    }

    n1.lemma_ValidCombine();
}

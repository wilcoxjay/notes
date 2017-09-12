// RUN: /print:log.bpl

predicate BijectiveMap<A,B>(m: imap<A,B>)
{
    && (forall x :: x in m)
    && (forall x1, x2 :: m[x1] == m[x2] ==> x1 == x2)
    && (forall y :: y in m.Values)
}

function InvertMap<A,B>(m: imap<A,B>): imap<B,A>
  requires BijectiveMap(m)
{
    imap b :: 
        assert b in m.Values;
        var a :| m[a] == b; 
        a
}

lemma lemma_InvertMapInverse<A,B>(m: imap<A,B>)
    requires BijectiveMap(m)
    ensures forall x :: InvertMap(m)[m[x]] == x
    ensures forall x :: m[InvertMap(m)[x]] == x
{}



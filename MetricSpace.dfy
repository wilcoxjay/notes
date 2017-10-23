// RUN: /nologo /rlimit:500000



module Prelude {
    function abs(x: real): real
    {
        if x < 0.0 then
            - x
        else
            x
    }

    function min(x: real, y: real): real
    {
        if x < y then
            x
        else
            y
    }
}

abstract module MetricSpace {
    type T

    function dist(x: T, y: T): real
        ensures 0.0 <= dist(x, y)

    lemma dist_sym(x: T, y: T)
        ensures dist(x, y) == dist(y, x)

    lemma dist_tri(x: T, y: T, z: T)
        ensures dist(x, z) <= dist(x, y) + dist(y, z)
}

module RMetricSpace
    refines MetricSpace
{
    import opened Prelude

    type T = real

    function dist(x: T, y: T): real
        ensures 0.0 <= dist(x, y)
    {
        abs(x - y)
    }

    lemma dist_sym(x: T, y: T)
        ensures dist(x, y) == dist(y, x)
    {}

/*    lemma dist_tri(x: T, y: T, z: T)
        ensures dist(x, z) <= dist(x, y) + dist(y, z)
    {}*/
}

abstract module TopologyOfAMetricSpace {
    import opened M : MetricSpace
    import opened Prelude

    function Ball(x: T, eps: real): iset<T>
    {
        iset y | dist(x, y) < eps
    }

    predicate Open(S: iset<T>)
    {
        forall x | x in S :: exists eps | eps > 0.0 :: Ball(x, eps) <= S
    }

    lemma OpenFamilyUnion(F: iset<iset<T>>)
        requires forall S | S in F :: Open(S)
        ensures Open(iset x, S | S in F && x in S :: x)
    {}

    lemma OpenUnion(S1: iset<T>, S2: iset<T>)
        requires Open(S1) && Open(S2)
        ensures Open(S1 + S2)
    {}

    predicate InAll(x: T, F: set<iset<T>>)
    {
        forall S | S in F :: x in S
    }

    lemma OpenFiniteFamilyIntersection(F: set<iset<T>>)
        requires forall S | S in F :: Open(S)
        ensures Open(iset x | InAll(x, F))
    {
        var I := iset x | InAll(x, F);

        if F == {} {
            forall x | x in I
                ensures exists eps | eps > 0.0 :: Ball(x, eps) <= I
            {
                assert Ball(x, 1.0) <= I;
            }
            return;
        }

        forall x | x in I
            ensures exists eps | eps > 0.0 :: Ball(x, eps) <= I
        {
            var acc: real;
            var todo := F;
            while todo != {}
                invariant todo <= F
                invariant todo != F ==> acc > 0.0
                invariant forall S | S in F && S !in todo :: Ball(x, acc) <= S
                decreases todo
            {
                var S :| S in todo;
                var eps :| eps > 0.0 && Ball(x, eps) <= S;
                if todo == F {
                    acc := eps;
                } else {
                    acc := min(eps, acc);
                }

                todo := todo - {S};
            }

            assert Ball(x, acc) <= I;
        }
    }

    lemma OpenIntersection(S1: iset<T>, S2: iset<T>)
        requires Open(S1) && Open(S2)
        ensures Open(S1 * S2)
    {}


    lemma Foo(x: T, y: T, z: T)
        ensures dist(x, z) <= dist(x, y) + dist(y, z)
    {
        dist_tri(x, y, z);
    }
}

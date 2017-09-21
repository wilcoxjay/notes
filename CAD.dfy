// RUN: /compile:0 /rlimit:500000

module PreludeModule {
    function abs(r: real): real
    {
        if r < 0.0 then
            - r
        else r
    }
    
    function min(a: real, b: real): real
    {
        if a < b then
            a
        else
            b
    }
    
    function max(a: real, b: real): real
    {
        if a > b then
            a
        else
            b
    }

    lemma ISetNonEmpty<A>(x: A, S: iset<A>)
        requires x in S
        ensures S != iset{}
    {}
}

module RealModule {
    import opened PreludeModule

    predicate InOpenInterval(a: real, b: real, x: real)
    {
        a < x < b
    }
    
    function OpenInterval(a: real, b: real): iset<real>
    {
        iset x | InOpenInterval(a, b, x)
    }
    
    predicate InClosedInterval(a: real, b: real, x: real)
    {
        a <= x <= b
    }
    
    function ClosedInterval(a: real, b: real): iset<real>
    {
        iset x | InClosedInterval(a, b, x)
    }

    predicate InTranslatedSet(r: real, S: iset<real>, x: real)
    {
        x - r in S
    }

    function TranslateSet(r: real, S: iset<real>): iset<real>
    {
        iset x | InTranslatedSet(r, S, x)
    }
    
    predicate InScaledSet(r: real, S: iset<real>, x: real)
        requires r != 0.0
    {
        x / r in S
    }

    function ScaleSet(r: real, S: iset<real>): iset<real>
    {
        if r == 0.0 then iset{}
        else iset x | InScaledSet(r, S, x)
    }

    predicate IsUB(x: real, S: iset<real>)
    {
        forall y | y in S :: y <= x
    }
    
    predicate IsLUB(x: real, S: iset<real>)
    {
        IsUB(x, S) && forall x' | IsUB(x', S) :: x <= x'
    }
    
    lemma {:axiom} LUBExists(S: iset<real>)
        requires exists x :: x in S
        requires exists x :: IsUB(x, S)
        ensures exists x :: IsLUB(x, S)
    
    function LUB(S: iset<real>): real
        requires exists x :: x in S
        requires exists x :: IsUB(x, S)
    {
        LUBExists(S);
        var x :| IsLUB(x, S);
        x
    }
    
    predicate IsLB(x: real, S: iset<real>)
    {
        forall y | y in S :: x <= y
    }
    
    predicate IsGLB(x: real, S: iset<real>)
    {
        IsLB(x, S) && forall x' | IsLB(x', S) :: x' <= x
    }
    
    lemma GLBExists(S: iset<real>)
        requires exists x :: IsLB(x, S)
        requires exists x :: x in S
        ensures exists x :: IsGLB(x, S)
    {
        var x :| x in S;
        var y :| IsLB(y, S);
        var LBs := iset x | IsLB(x, S);
        assert IsUB(x, LBs);
        assert y in LBs;
        LUBExists(LBs);
        var x' :| IsLUB(x', LBs);
        assert IsUB(x', LBs);
    
        forall y | IsLB(y, S)
            ensures y <= x'
        {
            assert y in LBs;
        }
        forall y | y in S
            ensures x' <= y
        {
            if y < x' {
                assert IsUB(y, LBs);
                assert false;
            }
        }
        assert IsGLB(x', S);
    }
    
    
    function GLB(S: iset<real>): real
        requires exists x :: x in S
        requires exists x :: IsLB(x, S)
    {
        GLBExists(S);
        var x :| IsGLB(x, S);
        x
    }
    
    predicate NonEmpty(S: iset<real>)
    {
        exists x :: x in S
    }
    
    predicate InBall(center: real, r: real, x: real)
    {
        abs(center - x) < r
    }
    
    function Ball(center: real, r: real): iset<real>
    {
        iset x | InBall(center, r, x)
    }
    
    predicate InClosure(x: real, S: iset<real>)
    {
        forall eps | eps > 0.0 :: !(Ball(x, eps) !! S)
    }
    
    function Closure(S: iset<real>): iset<real>
    {
        iset x | InClosure(x, S)
    }

    lemma ClosureOpenInterval(a: real, b: real)
        requires a < b
        ensures Closure(OpenInterval(a, b)) == ClosedInterval(a, b)
    {
        forall x | x in Closure(OpenInterval(a, b))
            ensures x in ClosedInterval(a, b)
        {
            if x < a {
                var eps := (a - x) / 2.0;
                var y :| y in Ball(x, eps) * OpenInterval(a, b);
            } else if x > b {
                var eps := (x - b) / 2.0;
                var y :| y in Ball(x, eps) * OpenInterval(a, b);
            }
        }
    
        forall x | x in ClosedInterval(a, b)
            ensures x in Closure(OpenInterval(a, b))
        {
            forall eps | eps > 0.0
                ensures Ball(x, eps) * OpenInterval(a, b) != iset{}
            {
                if x == a {
                    var d := min(eps, b - a) / 2.0;
                    assert x + d in Ball(a, eps);
                    ISetNonEmpty(x + d, Ball(a, eps) * OpenInterval(a, b));
                } else if x == b {
                    var d := min(eps, b - a) / 2.0;
                    ISetNonEmpty(x - d, Ball(b, eps) * OpenInterval(a, b));
                } else {
                    ISetNonEmpty(x, Ball(x, eps) * OpenInterval(a, b));
                }
            }
        }
    }
    
    lemma ClosureUnion(A: iset<real>, B: iset<real>)
        ensures Closure(A + B) == Closure(A) + Closure(B)
    { }
    
    lemma ClosureEmpty()
        ensures Closure(iset{}) == iset{}
    {
        forall x | x in Closure(iset{})
            ensures x in iset{}
        {
            var x' :| x' in Ball(x, 1.0) && x' in iset{};
            assert false;
        }
    }

    lemma CloseAdjacentOpenIntervals(a: real, b: real, c: real)
        requires a <= b <= c
        ensures Closure(OpenInterval(a, b) + OpenInterval(b, c)) == Closure(OpenInterval(a, c))
    {
        if a == b || b == c { return; }
    
        ClosureUnion(OpenInterval(a,b), OpenInterval(b,c));
        ClosureOpenInterval(a, c);
        ClosureOpenInterval(a, b);
        ClosureOpenInterval(b, c);
    }

    predicate InInterior(x: real, S: iset<real>)
    {
        exists eps | eps > 0.0 :: Ball(x, eps) <= S
    }
    
    function Interior(S: iset<real>): iset<real>
    {
        iset x | InInterior(x, S)
    }
    
    predicate Open(S: iset<real>)
    {
        forall x | x in S :: InInterior(x, S)
    }

    lemma InteriorSubset(S: iset<real>)
        ensures Interior(S) <= S
    {}


    lemma InteriorOpen(S: iset<real>)
        ensures Open(Interior(S))
    {
        forall x | x in Interior(S)
            ensures InInterior(x, Interior(S))
        {
            var eps :| eps > 0.0 && Ball(x, eps) <= S;
            forall y | y in Ball(x, eps)
                ensures y in Interior(S)
            {
                var eps' := eps - abs(x - y);
                assert Ball(y, eps') <= S;
            }
        }
    }


    lemma OpenIntervalOpen(a: real, b: real)
        requires a < b
        ensures Open(OpenInterval(a, b))
    {
        var S := OpenInterval(a, b);
        forall x | x in S
            ensures exists eps | eps > 0.0 :: Ball(x, eps) <= S
        {
            var eps := min((x - a) / 2.0, (b - x) / 2.0);
            assert Ball(x, eps) <= S;
        }
    }
    
    lemma TranslateSetOpen(r: real, S: iset<real>)
        requires Open(S)
        ensures Open(TranslateSet(r, S))
    {
        var S' := TranslateSet(r, S);
        forall x | x in S'
            ensures exists eps | eps > 0.0 :: Ball(x, eps) <= S'
        {
            var y := x - r;
            assert y in S;
            var eps :| eps > 0.0 && Ball(y, eps) <= S;
    
            assert Ball(x, eps) <= S';
        }
    }
    
    lemma ScaleSetOpen(r: real, S: iset<real>)
        requires Open(S)
        ensures Open(ScaleSet(r, S))
    {
        if r == 0.0 { return; }
        var S' := ScaleSet(r, S);
        forall x | x in S'
            ensures exists eps | eps > 0.0 :: Ball(x, eps) <= S'
        {
            var y := x / r;
            assert y in S;
            var eps :| eps > 0.0 && Ball(y, eps) <= S;
    
            assert Ball(x, abs(r) * eps) <= S';
        }
    }

    function R(): iset<real>
    {
        iset x {:nowarn} | true
    }
    
    predicate Closed(S: iset<real>)
    {
        S == Closure(S)
    }
    
    lemma ClosureSubset(S: iset<real>)
        ensures S <= Closure(S)
    {}
    
    lemma ClosureIdempotent(S: iset<real>)
        ensures Closure(Closure(S)) == Closure(S)
    {
        forall x | x in Closure(Closure(S))
            ensures x in Closure(S)
        {
            forall eps | eps > 0.0
                ensures !(Ball(x, eps) !! S)
            {
                var y :| y in Ball(x, eps / 2.0) && y in Closure(S);
                var z :| z in Ball(y, eps / 2.0) && z in S;
            }
        }
    }
    
    lemma ClosureClosed(S: iset<real>)
        ensures Closed(Closure(S))
    {
        ClosureIdempotent(S);
    }
    
    
    lemma DisjointIntersectionEmpty<T>(A: iset<T>, B: iset<T>)
        requires A * B == iset{}
        ensures A !! B
    {
        forall a, b | a in A && b in B
            ensures a != b
        {
            if a == b {
                assert a in A * B;
                ISetNonEmpty(a, A * B);
            }
        }
    }
    
    lemma ComplementClosedOpen(S: iset<real>)
        requires Closed(S)
        ensures Open(R() - S)
    {
        var D := R() - S;
        forall x | x in D
            ensures exists eps | eps > 0.0 :: Ball(x, eps) <= D
        {
            assert x !in Closure(S);
            var eps :| eps > 0.0 && Ball(x, eps) * S == iset{};
            DisjointIntersectionEmpty(Ball(x, eps), S);
            assert Ball(x, eps) <= D;
        }
    }
    
    lemma IntersectOpen(S1: iset<real>, S2: iset<real>)
        requires Open(S1) && Open(S2)
        ensures Open(S1 * S2)
    {}
    
    lemma DifferenceOpen(S1: iset<real>, S2: iset<real>)
        requires Open(S1)
        ensures Open(S1 - Closure(S2))
    {
        assert S1 - Closure(S2) == S1 * (R() - Closure(S2));
        ClosureClosed(S2);
        ComplementClosedOpen(Closure(S2));
        IntersectOpen(S1, R() - Closure(S2));
    }

    predicate RegularOpen(S: iset<real>)
    {
        S == Interior(Closure(S))
    }

    function RegularJoin(A: iset<real>, B: iset<real>): iset<real>
    {
        Interior(Closure(A + B))
    }

    lemma InteriorMonotonic(A: iset<real>, B: iset<real>)
        requires A <= B
        ensures Interior(A) <= Interior(B)
    {}

    lemma InteriorIdempotent(S: iset<real>)
        ensures Interior(Interior(S)) == Interior(S)
    {
        InteriorSubset(Interior(S));

        forall x | x in Interior(S)
            ensures x in Interior(Interior(S))
        {
            var eps :| eps > 0.0 && Ball(x, eps) <= S;
            forall y | y in Ball(x, eps)
                ensures y in Interior(S)
            {
                var eps' := eps - abs(x - y);
                assert Ball(y, eps') <= S;
            }
        }
    }

    lemma ClosureMonotonic(A: iset<real>, B: iset<real>)
        requires A <= B
        ensures Closure(A) <= Closure(B)
    {}


    lemma InteriorClosureInteriorClosure(S: iset<real>)
        ensures Interior(Closure(Interior(Closure(S)))) == Interior(Closure(S))
    {
        calc ==> {
            true;
            { ClosureSubset(Interior(Closure(S))); }
            Interior(Closure(S)) <= Closure(Interior(Closure(S)));
            { InteriorMonotonic(Interior(Closure(S)), Closure(Interior(Closure(S)))); }
            Interior(Interior(Closure(S))) <= Interior(Closure(Interior(Closure(S))));
            { InteriorIdempotent(Closure(S)); }
            Interior(Closure(S)) <= Interior(Closure(Interior(Closure(S))));
        }

        calc ==> {
            true;
            { InteriorSubset(Closure(S)); }
            Interior(Closure(S)) <= Closure(S);
            { ClosureMonotonic(Interior(Closure(S)), Closure(S)); }
            Closure(Interior(Closure(S))) <= Closure(Closure(S));
            { ClosureIdempotent(S); }
            Closure(Interior(Closure(S))) <= Closure(S);
            { InteriorMonotonic(Closure(Interior(Closure(S))), Closure(S)); }
            Interior(Closure(Interior(Closure(S)))) <= Interior(Closure(S));
        }
    }

    lemma InteriorClosureRegularOpen(S: iset<real>)
        ensures RegularOpen(Interior(Closure(S)))
    {
        InteriorClosureInteriorClosure(S);
    }

    lemma RegularJoinRegularOpen(A: iset<real>, B: iset<real>)
        requires RegularOpen(A) && RegularOpen(B)
        ensures RegularOpen(RegularJoin(A, B))
    {
        InteriorClosureRegularOpen(A + B);
    }

    lemma RegularOpenBallInClosure(A: iset<real>, x: real, eps: real)
        requires eps > 0.0 && RegularOpen(A) && Ball(x, eps) <= Closure(A)
        ensures Ball(x, eps) <= A
    {
        forall y | y in Ball(x, eps)
            ensures y in Interior(Closure(A))
        {
            var eps' := eps - abs(x - y);
            assert Ball(y, eps') <= Closure(A);
        }
    }


    lemma IntersectRegularOpen(A: iset<real>, B: iset<real>)
        requires RegularOpen(A) && RegularOpen(B)
        ensures RegularOpen(A * B)
    {
        forall x | x in A && x in B
            ensures x in Interior(Closure(A * B))
        {
            var eps_A :| eps_A > 0.0 && Ball(x, eps_A) <= Closure(A);
            var eps_B :| eps_B > 0.0 && Ball(x, eps_B) <= Closure(B);
            RegularOpenBallInClosure(A, x, eps_A);
            RegularOpenBallInClosure(B, x, eps_B);
            assert Ball(x, min(eps_A, eps_B)) <= A * B;
        }
    }

    lemma DifferenceRegularOpen(A: iset<real>, B: iset<real>)
        requires RegularOpen(A) && RegularOpen(B)
        ensures RegularOpen(A - Closure(B))
    {
        assert A - Closure(B) == A * (R() - Closure(B));
        IntersectRegularOpen(A, R() - Closure(B));
    }

    lemma EstablishRegularOpen(S: iset<real>)
        requires Open(S) && Interior(Closure(S)) <= S
        ensures RegularOpen(S)
    {}

    lemma RegularOpenOpen(S: iset<real>)
        requires RegularOpen(S)
        ensures Open(S)
    {
        InteriorOpen(Closure(S));
    }

    lemma ClosureTranslateSet(r: real, S: iset<real>)
        ensures Closure(TranslateSet(r, S)) == TranslateSet(r, Closure(S))
    {
        forall x
            ensures x in Closure(TranslateSet(r, S)) <==> x in TranslateSet(r, Closure(S))
        {
            var y := x - r;
            calc <==> {
                x in Closure(TranslateSet(r, S));
                forall eps | eps > 0.0 :: !(Ball(x, eps) !! TranslateSet(r, S));
                {
                    forall eps | eps > 0.0
                        ensures !(Ball(x, eps) !! TranslateSet(r, S)) <==> !(Ball(y, eps) !! S)
                    {
                        if !(Ball(y, eps) !! S) {
                            var z :| z in Ball(y, eps) && z in S;
                            assert z + r in Ball(x, eps) && z + r in TranslateSet(r, S);
                        }
                    }
                }
                forall eps | eps > 0.0 :: !(Ball(y, eps) !! S);
                x in TranslateSet(r, Closure(S));
            }
        }
    }

    lemma BallInTranslateSet(x: real, eps: real, r: real, S: iset<real>)
        requires Ball(x, eps) <= TranslateSet(r, S)
        ensures Ball(x - r, eps) <= S
    {
        forall y | y in Ball(x - r, eps)
            ensures y in S
        {
            assert y + r in Ball(x, eps);
        }
    }

    lemma TranslateSetRegularOpen(r: real, S: iset<real>)
        requires RegularOpen(S)
        ensures RegularOpen(TranslateSet(r, S))
    {
        RegularOpenOpen(S);
        TranslateSetOpen(r, S);
        forall x | x in Interior(Closure(TranslateSet(r, S)))
            ensures x in TranslateSet(r, S)
        {
            var eps :| eps > 0.0 && Ball(x, eps) <= Closure(TranslateSet(r, S));
            ClosureTranslateSet(r, S);
            BallInTranslateSet(x, eps, r, Closure(S));
        }
        EstablishRegularOpen(TranslateSet(r, S));
    }

    lemma ScaleBall(x: real, y: real, r: real, eps: real)
        requires r != 0.0 && y in Ball(x, eps)
        ensures y * r in Ball(x * r, eps * abs(r))
    { }


    lemma ClosureScaleSet(r: real, S: iset<real>)
        requires r != 0.0
        ensures Closure(ScaleSet(r, S)) == ScaleSet(r, Closure(S))
    {
        forall x
            ensures x in Closure(ScaleSet(r, S)) <==> x in ScaleSet(r, Closure(S))
        {
            var y := x / r;
            calc <==> {
                x in Closure(ScaleSet(r, S));
                forall eps | eps > 0.0 :: !(Ball(x, eps) !! ScaleSet(r, S));
                {
                    if forall eps | eps > 0.0 :: !(Ball(x, eps) !! ScaleSet(r, S)) {
                        forall eps | eps > 0.0
                            ensures !(Ball(y, eps) !! S)
                        {
                            assert !(Ball(x, eps * abs(r)) !! ScaleSet(r, S));
                        }
                    }
                    if forall eps | eps > 0.0 :: !(Ball(y, eps) !! S) {
                        forall eps | eps > 0.0
                            ensures !(Ball(x, eps) !! ScaleSet(r, S))
                        {
                            assert !(Ball(y, eps / abs(r)) !! S);
                            var z :| z in Ball(y, eps / abs(r)) && z in S;
                            var w := z * r;
                            calc ==> {
                                z in Ball(y, eps / abs(r));
                                { ScaleBall(y, z, r, eps / abs(r)); }
                                z * r in Ball(y * r, eps);
                                abs(x - w) < eps;
                            }
                            calc ==> {
                                z in S;
                                { assert (z * r) / r == z; }
                                z * r in ScaleSet(r, S);
                            }
                            assert w in Ball(x, eps) && w in ScaleSet(r, S);
                        }
                    }
                }
                forall eps | eps > 0.0 :: !(Ball(y, eps) !! S);
                x in ScaleSet(r, Closure(S));
            }
        }
    }

    lemma BallInScaleSet(x: real, eps: real, r: real, S: iset<real>)
        requires Ball(x, eps) <= ScaleSet(r, S) && r != 0.0
        ensures Ball(x / r, eps / abs(r)) <= S
    {
        forall y | y in Ball(x / r, eps / abs(r))
            ensures y in S
        {
            calc ==> {
                y in Ball(x / r, eps / abs(r));
                { ScaleBall(x / r, y, r, eps / abs(r)); }
                y * r in Ball(x, eps);
                y * r in ScaleSet(r, S);
                { assert (y * r) / r == y; }
                y in S;
            }
        }
    }


    lemma ScaleSetRegularOpen(r: real, S: iset<real>)
        requires RegularOpen(S)
        ensures RegularOpen(ScaleSet(r, S))
    {
        if r == 0.0 { ClosureEmpty(); return; }
        RegularOpenOpen(S);
        ScaleSetOpen(r, S);
        forall x | x in Interior(Closure(ScaleSet(r, S)))
            ensures x in ScaleSet(r, S)
        {
            var eps :| eps > 0.0 && Ball(x, eps) <= Closure(ScaleSet(r, S));
            ClosureScaleSet(r, S);
            BallInScaleSet(x, eps, r, Closure(S));
        }
        EstablishRegularOpen(ScaleSet(r, S));
    }
}

module BoundedModule {
    import opened PreludeModule
    import opened RealModule

    predicate Bounded(S: iset<real>)
    {
        && (exists x :: IsLB(x, S))
        && (exists x :: IsUB(x, S))
    }

    lemma EmptyBounded()
        ensures Bounded(iset{})
    {
        assert IsLB(0.0, iset{});
        assert IsUB(0.0, iset{});
    }
    
    lemma OpenIntervalBounded(a: real, b: real)
        ensures Bounded(OpenInterval(a, b))
    {
        assert IsLB(a, OpenInterval(a, b));
        assert IsUB(b, OpenInterval(a, b));
    }
    
    lemma TranslateSetBounded(r: real, S: iset<real>)
        requires Bounded(S)
        ensures Bounded(TranslateSet(r, S))
    {
        var a :| IsLB(a, S);
        var b :| IsUB(b, S);
        assert IsLB(a + r, TranslateSet(r, S));
        assert IsUB(b + r, TranslateSet(r, S));
    }
    
    lemma ScaleSetBounded(r: real, S: iset<real>)
        requires Bounded(S)
        ensures Bounded(ScaleSet(r, S))
    {
        var a :| IsLB(a, S);
        var b :| IsUB(b, S);
        if r == 0.0 {
            EmptyBounded();
        } else if r > 0.0 {
            assert IsLB(a * r, ScaleSet(r, S));
            forall y | y in ScaleSet(r, S)
                ensures y <= b * r
            {}
            assert IsUB(b * r, ScaleSet(r, S));
        } else {
            assert IsLB(b * r, ScaleSet(r, S));
            assert IsUB(a * r, ScaleSet(r, S));
        }
    }
    
    lemma IntersectBounded(A: iset<real>, B: iset<real>)
        requires Bounded(A)
        ensures Bounded(A * B)
    {
        var a :| IsLB(a, A);
        var b :| IsUB(b, A);
        assert IsLB(a, A * B);
        assert IsUB(b, A * B);
    }
    
    lemma UnionBounded(A: iset<real>, B: iset<real>)
        requires Bounded(A) && Bounded(B)
        ensures Bounded(A + B)
    {
        var la :| IsLB(la, A);
        var ua :| IsUB(ua, A);
    
        var lb :| IsLB(lb, B);
        var ub :| IsUB(ub, B);
    
        assert IsLB(min(la, lb), A + B);
        assert IsUB(max(ua, ub), A + B);
    }
    
    lemma DifferenceBounded(A: iset<real>, B: iset<real>)
        requires Bounded(A)
        ensures Bounded(A - B)
    {
        assert A - B == A * (R() - B);
        IntersectBounded(A, R() - B);
    }

    function BBox(S: iset<real>): (real, real)
        requires NonEmpty(S) && Bounded(S)
    {
        GLBExists(S);
        LUBExists(S);
        var a :| IsGLB(a, S);
        var b :| IsLUB(b, S);
        (a, b)
    }
}

module CADModule {
    import opened PreludeModule
    import opened RealModule
    import opened BoundedModule

    datatype Expr =
        | Empty
        | Unit
        | Translate(r: real, e: Expr)
        | Scale(r: real, e: Expr)
        | Home(r: real, e: Expr)
        | Intersect(e1: Expr, e2: Expr)
        | Union(e1: Expr, e2: Expr)
        | Difference(e1: Expr, e2: Expr)
    
    
    // The following example shows that the semantics of difference cannot
    // be A - B, but must be A - cl(B)
    
    function HalfOpenInterval(): iset<real>
    {
        OpenInterval(-0.5, 0.5) - OpenInterval(0.0, 0.5)
    }
    
    // Construct the singleton set containing 0.0
    lemma Bad()
        ensures forall x | x in HalfOpenInterval() && x in ScaleSet(-1.0, HalfOpenInterval()) :: x == 0.0
    {}

    // ⦇e⦈
    function OpenDenote(e: Expr): (S: iset<real>)
        ensures Bounded(S)
    {
        match e
            case Empty =>
                EmptyBounded();
                iset{}
            case Unit =>
                OpenIntervalBounded(0.0, 1.0);
                OpenInterval(0.0, 1.0)
            case Translate(r,e) =>
                TranslateSetBounded(r, OpenDenote(e));
                TranslateSet(r, OpenDenote(e))
            case Home(r, e) => var S' := OpenDenote(e);
                TranslateSetBounded(-RelPos(r, S'), S');
                TranslateSet(-RelPos(r, S'), S')
            case Scale(r,e) =>
                ScaleSetBounded(r, OpenDenote(e));
                ScaleSet(r, OpenDenote(e))
            case Intersect(e1,e2) =>
                IntersectBounded(OpenDenote(e1), OpenDenote(e2));
                OpenDenote(e1) * OpenDenote(e2)
            case Union(e1,e2) =>
                UnionBounded(OpenDenote(e1), OpenDenote(e2));
                OpenDenote(e1) + OpenDenote(e2)
            case Difference(e1,e2) =>
                DifferenceBounded(OpenDenote(e1), Closure(OpenDenote(e2)));
                OpenDenote(e1) - Closure(OpenDenote(e2))
    }

    // ⟦e⟧
    function Denote(e: Expr): iset<real>
    {
        Closure(OpenDenote(e))
    }

    lemma UnionUnitTest()
        ensures Denote(Union(Unit, Translate(1.0, Unit))) == Denote(Scale(2.0, Unit))
    {
        calc {
            Denote(Union(Unit, Translate(1.0, Unit)));
            == Closure(OpenDenote(Union(Unit, Translate(1.0, Unit))));
            == Closure(OpenInterval(0.0, 1.0) + TranslateSet(1.0, OpenInterval(0.0, 1.0)));
            == Closure(OpenInterval(0.0, 1.0) + OpenInterval(1.0, 2.0));
            == { CloseAdjacentOpenIntervals(0.0, 1.0, 2.0); }
               Closure(OpenInterval(0.0, 2.0));
            == Closure(ScaleSet(2.0, OpenInterval(0.0, 1.0)));
            == Closure(OpenDenote(Scale(2.0, Unit)));
            == Denote(Scale(2.0, Unit));
        }
    }
    
    lemma DiffUnitTest()
        ensures Denote(Difference(Unit, Translate(1.0, Unit))) == Denote(Unit)
    {
        calc {
            Denote(Difference(Unit, Translate(1.0, Unit)));
            Closure(OpenInterval(0.0, 1.0) - Closure(TranslateSet(1.0, OpenInterval(0.0, 1.0))));
            == Closure(OpenInterval(0.0, 1.0) - Closure(OpenInterval(1.0, 2.0)));
            == { ClosureOpenInterval(1.0, 2.0); }
               Closure(OpenInterval(0.0, 1.0) - ClosedInterval(1.0, 2.0));
            == Denote(Unit);
        }
    }
    
    // Look ma, no proof!
    lemma IntersectUnitTest()
        ensures Denote(Intersect(Unit, Translate(1.0, Unit))) == Denote(Empty)
    {}
    
    lemma OpenDenoteOpen(e: Expr)
        ensures Open(OpenDenote(e))
    {
        match e {
            case Empty =>
            case Unit => OpenIntervalOpen(0.0, 1.0);
            case Translate(r, e) => TranslateSetOpen(r, OpenDenote(e));
            case Home(r, e) => var S := OpenDenote(e);
                TranslateSetOpen(-RelPos(r, S), S);
            case Scale(r, e) => { ScaleSetOpen(r, OpenDenote(e)); }
            case Intersect(e1, e2) => {}
            case Union(e1, e2) => {}
            case Difference(e1, e2) => { DifferenceOpen(OpenDenote(e1), OpenDenote(e2)); }
        }
    }
    
    predicate NoIsolatedPoints(S: iset<real>)
    {
        forall x, eps | x in S && eps > 0.0 :: !((Ball(x, eps) - iset{x}) !! S)
    }
    
    lemma DenoteNoIsolatedPoints(e: Expr)
        ensures NoIsolatedPoints(Denote(e))
    {
        forall x, eps | x in Denote(e) && eps > 0.0
            ensures exists z :: z in Ball(x, eps) && z != x && z in Denote(e)
        {
            assert !(OpenDenote(e) !! Ball(x, eps / 2.0));
            var y :| y in OpenDenote(e) && y in Ball(x, eps / 2.0);
            if x == y {
                OpenDenoteOpen(e);
                var eps' :| eps' > 0.0 && Ball(y, eps') <= OpenDenote(e);
                var eps'' := min(eps, eps') / 2.0;
                var z := x + eps'';
                assert z in Ball(y, eps');
                assert z in Denote(e);
            } else {
                assert y in Denote(e);
            }
    
        }
    }
    
    predicate HasNearbyPointInInterior(S: iset<real>, x: real, eps: real)
    {
        exists x', eps' | eps' > 0.0 :: Ball(x', eps') <= (Ball(x, eps) * S)
    }
    
    predicate NoInfinitelyThinFeatures(S: iset<real>)
    {
        forall x, eps | x in S && eps > 0.0 ::
            HasNearbyPointInInterior(S, x, eps)
    }
    
    lemma DenoteNoInfinitelyThinFeatures(e: Expr)
        ensures NoInfinitelyThinFeatures(Denote(e))
    {
        var S := Denote(e);
        forall x, eps | x in S && eps > 0.0
            ensures HasNearbyPointInInterior(S, x, eps)
        {
            assert x in Closure(OpenDenote(e));
            var x' :| x' in Ball(x, eps) && x' in OpenDenote(e);
            OpenDenoteOpen(e);
            var eps' :| eps' > 0.0 && Ball(x', eps') <= OpenDenote(e);
    
            var eps'' := min(eps', eps - abs(x - x'));
            assert Ball(x', eps'') <= OpenDenote(e);
        }
    }
    
    predicate AlternativeNoInfinitelyThinFeatures(S: iset<real>)
    {
        S <= Closure(Interior(S))
    }
    
    lemma AlternativeNoInfinitelyThinFeaturesEquiv(S: iset<real>)
        ensures AlternativeNoInfinitelyThinFeatures(S) <==> NoInfinitelyThinFeatures(S)
    {
        if AlternativeNoInfinitelyThinFeatures(S) {
            forall x, eps | x in S && eps > 0.0
                ensures HasNearbyPointInInterior(S, x, eps)
            {
                var x' :| x' in Ball(x, eps) && x' in Interior(S);
                var eps' :| eps' > 0.0 && Ball(x', eps') <= S;
                var eps'' := min(eps', eps - abs(x - x'));
                assert Ball(x', eps'') <= Ball(x, eps);
            }
        }
    
        if NoInfinitelyThinFeatures(S) {
            forall x | x in S
                ensures x in Closure(Interior(S))
            {
                forall eps | eps > 0.0
                    ensures !(Ball(x, eps) !! Interior(S))
                {
                    assert HasNearbyPointInInterior(S, x, eps);
                    var x', eps' :| eps' > 0.0 && Ball(x', eps') <= (Ball(x, eps) * S);
                    assert x' in Ball(x', eps');
                }
            }
        }
    }
    
    function RelPos(r: real, S: iset<real>): real
        requires Bounded(S)
    {
        if S == iset{} then
            0.0  // dummy value
        else
            var (a, b) := BBox(S);
            a + r * (b - a)
    }
    
    predicate Equiv(e1: Expr, e2: Expr)
    {
        Denote(e1) == Denote(e2)
    }
    
    lemma SelfUnion(e: Expr)
        ensures Equiv(Union(e, e), e)
    {}
    
    lemma SelfIntersect(e: Expr)
        ensures Equiv(Intersect(e, e), e)
    {}
    
    lemma SelfDifference(e: Expr)
        ensures Equiv(Difference(e, e), Empty)
    {}
    
    lemma UnionEmpty(e: Expr)
        ensures Equiv(Union(e, Empty), e)
    {}
    
    lemma IntersectEmpty(e: Expr)
        ensures Equiv(Intersect(e, Empty), Empty)
    {}
    
    
    lemma DifferenceEmpty1(e: Expr)
        ensures Equiv(Difference(e, Empty), e)
    {
        calc {
            Denote(Difference(e, Empty));
            Closure(OpenDenote(e) - Closure(iset{}));
            { ClosureEmpty(); }
            Closure(OpenDenote(e));
            Denote(e);
        }
    }
    
    lemma DifferenceEmpty2(e: Expr)
        ensures Equiv(Difference(Empty, e), Empty)
    {}
    
    lemma UnionComm(e1: Expr, e2: Expr)
        ensures Equiv(Union(e1, e2), Union(e2, e1))
    {}
    
    lemma IntersectComm(e1: Expr, e2: Expr)
        ensures Equiv(Intersect(e1, e2), Intersect(e2, e1))
    {}
    
    lemma UnionAssoc(e1: Expr, e2: Expr, e3: Expr)
        ensures Equiv(Union(e1, Union(e2, e3)), Union(Union(e1, e2), e3))
    {
        assert
            OpenDenote(e1) + (OpenDenote(e2) + OpenDenote(e3)) ==
            (OpenDenote(e1) + OpenDenote(e2)) + OpenDenote(e3);
    }
    
    lemma IntersectAssoc(e1: Expr, e2: Expr, e3: Expr)
        ensures Equiv(Intersect(e1, Intersect(e2, e3)), Intersect(Intersect(e1, e2), e3))
    {
        assert
            OpenDenote(e1) * (OpenDenote(e2) * OpenDenote(e3)) ==
            (OpenDenote(e1) * OpenDenote(e2)) * OpenDenote(e3);
    }
    
    lemma IntersectDifference(e1: Expr, e2: Expr)
        ensures Equiv(Intersect(e1, e2), Difference(e1, Difference(e1, e2)));
    {
        calc {
            Denote(Intersect(e1, e2));
            Closure(OpenDenote(Intersect(e1, e2)));
            Closure(OpenDenote(e1) * OpenDenote(e2));
            {
                assert OpenDenote(e1) * OpenDenote(e2) ==
                    OpenDenote(e1) - Closure(OpenDenote(e1) - Closure(OpenDenote(e2)))
                by {
                    var S1 := OpenDenote(e1);
                    var S2 := OpenDenote(e2);
                    OpenDenoteOpen(e2);
                    
                    forall x | x in S1 && x in S2
                        ensures x in S1 - Closure(S1 - Closure(S2))
                    {
                        var eps :| Ball(x, eps) <= S2;
                    }
                    forall x | x in S1 && x !in Closure(S1 - Closure(S2))
                        ensures x in S1 * S2
                    {}
                }
            }
            Closure(OpenDenote(e1) - Closure(OpenDenote(e1) - Closure(OpenDenote(e2))));
            Closure(OpenDenote(Difference(e1, Difference(e1, e2))));
            Denote(Difference(e1, Difference(e1, e2)));
        }
    }
}

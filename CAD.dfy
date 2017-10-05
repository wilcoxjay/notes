// RUN: /compile:0 /rlimit:500000 /vcsCores:4

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

    lemma EmptySubtractSubset<T>(A: iset<T>, B: iset<T>)
        ensures A - B == iset{} <==> A <= B
    {
        if A - B == iset{} {
            forall x | x in A
                ensures x in B
            {
                if x !in B {
                    assert x in A - B;
                    ISetNonEmpty(x, A - B);
                    assert false;
                }
            }
        }
    }
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

    predicate LEModuloEpsilon(x: real, y: real, eps: real)
    {
        x <= y + eps
    }

    lemma EstablishLE(x: real, y: real)
        requires forall eps | eps > 0.0 :: LEModuloEpsilon(x, y, eps)
        ensures x <= y
    {
        if x > y {
            var eps := x - y;
            assert LEModuloEpsilon(x, y, eps / 2.0);
        }
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
                ensures !(Ball(x, eps) !! OpenInterval(a, b))
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

    lemma InteriorClosedInterval(a: real, b: real)
        ensures Interior(ClosedInterval(a, b)) == OpenInterval(a, b)
    {
        forall x | x in Interior(ClosedInterval(a, b))
            ensures x in OpenInterval(a, b)
        {
            var eps :| eps > 0.0 && Ball(x, eps) <= ClosedInterval(a, b);
            assert x - eps / 2.0 in Ball(x, eps);
            assert x + eps / 2.0 in Ball(x, eps);
            assert a <= x - eps / 2.0 < x < x + eps / 2.0 <= b;
        }

        forall x | x in OpenInterval(a, b)
            ensures x in Interior(ClosedInterval(a, b))
        {
            var eps := min(x - a, b - x);
            assert Ball(x, eps) <= ClosedInterval(a, b);
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

    lemma UnionOpen(S1: iset<real>, S2: iset<real>)
        requires Open(S1) && Open(S2)
        ensures Open(S1 + S2)
    {}

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

    predicate Regular(S: iset<real>)
    {
        Interior(Closure(S)) <= S <= Closure(Interior(S))
    }

    predicate Regularizable(S: iset<real>)
    {
        Interior(Closure(S)) <= Closure(Interior(S))
    }

    lemma OpenInteriorNop(S: iset<real>)
        requires Open(S)
        ensures Interior(S) == S
    {}

    lemma RegularOpenRegular(S: iset<real>)
        requires RegularOpen(S)
        ensures Regular(S)
    {
        RegularOpenOpen(S);
        OpenInteriorNop(S);
        ClosureSubset(S);
    }

    lemma RegularOpenIffRegularAndOpen(S: iset<real>)
        ensures RegularOpen(S) <==> Regular(S) && Open(S)
    {
        if RegularOpen(S) {
            RegularOpenOpen(S);
            RegularOpenRegular(S);
            assert Regular(S) && Open(S);
        }
    }


    predicate RegularizableOpen(S: iset<real>)
    {
        && Regularizable(S)
        && Open(S)
    }


    predicate RegularOpen(S: iset<real>)
    {
        S == Interior(Closure(S))
    }

    lemma RegularOpenEmpty()
        ensures RegularOpen(iset{})
    {
        ClosureEmpty();
    }

    function RegularJoin(A: iset<real>, B: iset<real>): iset<real>
    {
        Interior(Closure(A + B))
    }

    function RegularJoinAlt(A: iset<real>, B: iset<real>): iset<real>
    {
        (A + B) + (Closure(A) * Closure(B))
    }

    predicate RegularEquiv(A: iset<real>, B: iset<real>)
    {
        Interior(Closure(A)) == Interior(Closure(B))
    }

    predicate RegularApprox(A: iset<real>, B: iset<real>)
    {
        Interior(Closure(A)) <= Interior(Closure(B))
    }

    lemma RegularizableBall(S: iset<real>, x: real, eps: real) returns (x': real, eps': real)
        requires eps > 0.0 && Regularizable(S) && Ball(x, eps) <= Closure(S)
        ensures eps' > 0.0 && Ball(x', eps') <= Ball(x, eps) * S
    {
        assert Interior(Closure(S)) <= Closure(Interior(S));
        assert x in Ball(x, eps) && x in Interior(Closure(S));
        assert !(Ball(x, eps) !! Interior(S));
        x' :| x' in Ball(x, eps) && x' in Interior(S);
        eps' :| eps' > 0.0 && Ball(x', eps') <= S;
        eps' := min(eps', eps - abs(x - x'));
    }

    predicate NowhereDense(S: iset<real>)
    {
        Interior(Closure(S)) == iset{}
    }

    function Boundary(S: iset<real>): iset<real>
    {
        Closure(S) - Interior(S)
    }

    lemma ComplementOpenClosed(S: iset<real>)
        requires Open(S)
        ensures Closed(R() - S)
    {}

    lemma IntersectClosed(A: iset<real>, B: iset<real>)
        requires Closed(A) && Closed(B)
        ensures Closed(A * B)
    {}

    lemma BoundaryClosed(S: iset<real>)
        ensures Closed(Boundary(S))
    {
        assert Boundary(S) == Closure(S) * (R() - Interior(S));
        InteriorOpen(S);
        ComplementOpenClosed(Interior(S));
        ClosureClosed(S);
        IntersectClosed(Closure(S), R() - Interior(S));
    }

    lemma RegularizableIffNowhereDenseBoundary(S: iset<real>)
        ensures Regularizable(S) <==> NowhereDense(Boundary(S))
    {
        calc <==> {
            Regularizable(S);
            Interior(Closure(S)) <= Closure(Interior(S));
            { EmptySubtractSubset(Interior(Closure(S)), Closure(Interior(S))); }
            Interior(Closure(S)) - Closure(Interior(S)) == iset{};
            Interior(Closure(S) * (R() - Interior(S))) == iset{};
            Interior(Closure(S) - Interior(S)) == iset{};
            Interior(Boundary(S)) == iset{};
            { BoundaryClosed(S); }
            Interior(Closure(Boundary(S))) == iset{};
            NowhereDense(Boundary(S));
        }
    }

    lemma BoundaryUnionSubset(A: iset<real>, B: iset<real>)
        ensures Boundary(A + B) <= Boundary(A) + Boundary(B)
    {}

    lemma NowhereDenseSubset(A: iset<real>, B: iset<real>)
        requires A <= B && NowhereDense(B)
        ensures NowhereDense(A)
    {}

    lemma NowhereDenseAlternative(S: iset<real>)
        ensures NowhereDense(S) <==> forall x, eps | eps > 0.0 :: !(Ball(x, eps) !! (R() - Closure(S)))
    {
        if NowhereDense(S) {
            forall x, eps | eps > 0.0
                ensures Ball(x, eps) - Closure(S) != iset{}
            {
                if  Ball(x, eps) - Closure(S) == iset{} {
                    assert x in Ball(x, eps);
                    EmptySubtractSubset(Ball(x, eps), Closure(S));
                    assert Ball(x, eps) <= Closure(S);
                    ISetNonEmpty(x, Interior(Closure(S)));
                    assert false;
                }
            }

            assert forall x, eps | eps > 0.0 :: Ball(x, eps) - Closure(S) != iset{};
        }

        if forall x, eps | eps > 0.0 :: Ball(x, eps) - Closure(S) != iset{} {
            if Interior(Closure(S)) != iset{} {
                var x :| x in Interior(Closure(S));
                var eps :| eps > 0.0 && Ball(x, eps) <= Closure(S);
                assert false;
            }

            assert NowhereDense(S);
        }
    }


    lemma NowhereDenseUnion(A: iset<real>, B: iset<real>)
        requires NowhereDense(A) && NowhereDense(B)
        ensures NowhereDense(A + B)
    {
        forall x, eps | eps > 0.0
            ensures !(Ball(x, eps) !! (R() - Closure(A + B)))
        {
            assert !(Ball(x, eps) !! (R() - Closure(A))) by {
                NowhereDenseAlternative(A);
            }
            var y :| y in Ball(x, eps) && y !in Closure(A);
            var eps' :| eps' > 0.0 && Ball(y, eps') !! A;
            var eps'' := min(eps', eps - abs(x - y));
            assert !(Ball(y, eps'') !! (R() - Closure(B))) by {
                NowhereDenseAlternative(B);
            }
            var z :| z in Ball(y, eps'') && z !in Closure(B);
            var eps''' := eps'' - abs(z - y);
            assert z in Ball(z, eps''') && Ball(z, eps''') <= Ball(y, eps'');
            assert z !in Closure(A);
            assert z in Ball(x, eps);
            assert z !in Closure(A + B);
        }
    }

    lemma NowhereDenseBoundaryUnion(A: iset<real>, B: iset<real>)
        requires NowhereDense(Boundary(A)) && NowhereDense(Boundary(B))
        ensures NowhereDense(Boundary(A + B))
    {
        BoundaryUnionSubset(A, B);
        NowhereDenseUnion(Boundary(A), Boundary(B));
        NowhereDenseSubset(Boundary(A + B), Boundary(A) + Boundary(B));
    }

    lemma InteriorUnion(A: iset<real>, B: iset<real>)
        ensures Interior(A) + Interior(B) <= Interior(A + B)
    {}

    lemma RegularizableUnion(A: iset<real>, B: iset<real>)
        requires Regularizable(A) && Regularizable(B)
        ensures Regularizable(A + B)
    {
        forall S
            ensures Regularizable(S) <==> NowhereDense(Boundary(S))
        {
            RegularizableIffNowhereDenseBoundary(S);
        }
        NowhereDenseBoundaryUnion(A, B);

    }

    lemma ExploitClosureOfInterior(A: iset<real>, x: real, eps: real)
        returns (x': real, eps': real)
        requires eps > 0.0 && x in Closure(Interior(A))
        ensures eps' > 0.0 && Ball(x', eps') <= A * Ball(x, eps)
    {
        assert !(Interior(A) !! Ball(x, eps));
        x' :| x' in Interior(A) && x' in Ball(x, eps);
        eps' :| eps' > 0.0 && Ball(x', eps') <= A;
        eps' := min(eps - abs(x - x'), eps');
    }

    lemma SomethingBallUnion(A: iset<real>, B: iset<real>, x: real, eps: real)
        returns (x': real, eps': real)
        requires eps > 0.0 && Ball(x, eps) <= A + B
        requires A <= Closure(Interior(A)) && B <= Closure(Interior(B))
        ensures eps' > 0.0
        ensures
            || Ball(x', eps') <= Ball(x, eps) * A
            || Ball(x', eps') <= Ball(x, eps) * B
    {
        assert x in Ball(x, eps);
        if x in A {
            x', eps' := ExploitClosureOfInterior(A, x, eps);
        } else {
            assert x in B;
            x', eps' := ExploitClosureOfInterior(B, x, eps);
        }
    }

    lemma RegularApproxUnion(A: iset<real>, B: iset<real>, A': iset<real>)
        requires RegularApprox(A, A') && RegularizableOpen(A)
        ensures RegularApprox(A + B, A' + B)
    {
        var U := A + B;
        var V := A' + B;
        forall x | x in Interior(Closure(U))
            ensures x in Interior(Closure(V))
        {
            calc ==> {
                x in Interior(Closure(A + B));
                exists eps :: eps > 0.0 && Ball(x, eps) <= Closure(A + B);
                {
                    var eps :| eps > 0.0 && Ball(x, eps) <= Closure(A + B);

                    forall y | y in Ball(x, eps)
                        ensures y in Closure(A' + B)
                    {
                        forall eps' | eps' > 0.0
                            ensures !(Ball(y, eps') !! (A' + B))
                        {
                            assert !(Ball(y, eps') !! (A + B));
                            var z :| z in Ball(y, eps') && z in A + B;
                            if z in A {
                                var eps'' :| eps'' > 0.0 && Ball(z, eps'') <= A;
                                assert z in Interior(A) && z in Interior(Closure(A));
                                assert z in Interior(Closure(A'));
                                var eps''' :| eps''' > 0.0 && Ball(z, eps''') <= Closure(A');
                                var eps'''' := min(eps''', eps' - abs(z - y));
                                assert z in Ball(z, eps''');
                                assert z in Closure(A');
                                assert !(Ball(z, eps'''') !! A');
                                assert !(Ball(y, eps') !! (A' + B));
                            } else {
                                assert z in B;
                                assert !(Ball(y, eps') !! (A' + B));
                            }
                        }
                    }
                }
                exists eps :: eps > 0.0 && Ball(x, eps) <= Closure(A' + B);
                x in Interior(Closure(A' + B));
            }
        }
    }

    lemma RegularEquivUnion(A: iset<real>, B: iset<real>, A': iset<real>)
        requires RegularEquiv(A, A') && RegularizableOpen(A) && RegularizableOpen(A')
        ensures RegularEquiv(A + B, A' + B)
    {
        RegularApproxUnion(A, B, A');
        RegularApproxUnion(A', B, A);
    }

    lemma RegularEquivRegularJoin(A: iset<real>, B: iset<real>)
        ensures RegularEquiv(RegularJoin(A, B), A + B)
    {
        InteriorClosureInteriorClosure(A + B);
    }

    lemma RegularJoinAssoc(A: iset<real>, B: iset<real>, C: iset<real>)
        requires RegularizableOpen(A) && RegularizableOpen(B) && RegularizableOpen(C)
        ensures RegularJoin(RegularJoin(A, B), C) == RegularJoin(A, RegularJoin(B, C))
    {
        forall x
            ensures x in RegularJoin(RegularJoin(A, B), C) <==>
                    x in RegularJoin(A, RegularJoin(B, C))
        {
            calc <==> {
                x in RegularJoin(RegularJoin(A, B), C);
                x in Interior(Closure(RegularJoin(A, B) + C));
                { RegularEquivRegularJoin(A, B);
                  RegularJoinRegularOpen(A, B);
                  RegularOpenRegular(RegularJoin(A, B));
                  RegularOpenOpen(RegularJoin(A, B));
                  RegularizableUnion(A, B);
                  UnionOpen(A, B);
                  RegularEquivUnion(RegularJoin(A, B), C, A + B);
                }
                x in Interior(Closure(A + B + C));
                { assert A + B + C == (B + C) + A; }
                x in Interior(Closure((B + C) + A));
                { RegularEquivRegularJoin(B, C);
                  RegularJoinRegularOpen(B, C);
                  RegularOpenRegular(RegularJoin(B, C));
                  RegularOpenOpen(RegularJoin(B, C));
                  RegularizableUnion(B, C);
                  UnionOpen(B, C);
                  RegularEquivUnion(RegularJoin(B, C), A, B + C);
                }
                x in Interior(Closure(RegularJoin(B, C) + A));
                { assert RegularJoin(B, C) + A == A + RegularJoin(B, C); }
                x in Interior(Closure(A + RegularJoin(B, C)));
                x in RegularJoin(A, RegularJoin(B, C));
            }
        }

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

    lemma OpenIntervalRegularOpen(a: real, b: real)
        ensures RegularOpen(OpenInterval(a, b))
    {
        if b <= a {
            RegularOpenEmpty();
            assert OpenInterval(a, b) == iset{};
            return;
        }
        ClosureOpenInterval(a, b);
        InteriorClosedInterval(a, b);
    }

    lemma RegularJoinRegularOpen(A: iset<real>, B: iset<real>)
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
    {
        assert InBall(x * r, eps * abs(r), y * r);
    }


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

    predicate InHullSet(S: iset<real>, x: real)
    {
        exists p, q :: p in S && q in S && p < x < q
    }

    function HullSet(S: iset<real>): iset<real>
    {
        iset x | InHullSet(S, x)
    }

    lemma HullSetOpen(S: iset<real>)
        ensures Open(HullSet(S))
    {
        forall x | x in HullSet(S)
            ensures exists eps :: eps > 0.0 && Ball(x, eps) <= HullSet(S)
        {
            var p, q :| p in S && q in S && p < x < q;
            var eps := min(x - p, q - x);
            assert Ball(x, eps) <= HullSet(S);
        }
    }

    lemma HullSetRegularOpen(S: iset<real>)
        ensures RegularOpen(HullSet(S))
    {
        forall x | x in Interior(Closure(HullSet(S)))
            ensures x in HullSet(S)
        {
            var eps :| eps > 0.0 && Ball(x, eps) <= Closure(HullSet(S));
            var p := x - eps / 2.0;
            var q := x + eps / 2.0;
            assert p in Ball(x, eps) && q in Ball(x, eps);
            assert !(Ball(p, eps / 2.0) !! HullSet(S));
            assert !(Ball(q, eps / 2.0) !! HullSet(S));
            var p' :| p' in Ball(p, eps / 2.0) && p' in HullSet(S);
            var q' :| q' in Ball(q, eps / 2.0) && q' in HullSet(S);
            var p'' :| p'' in S && p'' < p';
            var q'' :| q'' in S && q' < q'';
        }

        HullSetOpen(S);
        EstablishRegularOpen(HullSet(S));
    }
}

module SqrtModule {
    function Square(x: real): (y: real)
        ensures y >= 0.0
    {
        x * x
    }

    function Sqrt(x: real): (y: real)
        requires x >= 0.0
        ensures y >= 0.0 && Square(y) == x

    lemma MulLtCompat(a: real, b: real, c: real)
        requires a < b
        requires c > 0.0
        ensures a * c < b * c
    {}
    
    lemma SquareGtZero(x: real)
        ensures x > 0.0 ==> Square(x) > 0.0
    {
        if x > 0.0 {
            MulLtCompat(0.0, x, x);
        }
    }
    
    lemma SquareEqZero(x: real)
        ensures Square(x) == 0.0 ==> x == 0.0
    {
        if x * x == 0.0 {
            if x > 0.0 {
                SquareGtZero(x);
            } else if x < 0.0 {
                var y := -x;
                assert Square(x) == Square(y);
                SquareGtZero(y);
            }
        }
    }
    
    lemma SqrtZero()
        ensures Sqrt(0.0) == 0.0
    {
        var x := Sqrt(0.0);
        assert Square(x) == 0.0;
        SquareGtZero(x);
    }
}

module Real2dModule {
    import opened SqrtModule
    import opened PreludeModule

    datatype Point2d = Point2d(x: real, y: real)
    
    function Add(p1: Point2d, p2: Point2d): Point2d
    {
        Point2d(p1.x + p2.x, p1.y + p2.y)
    }

    function Subtract(p1: Point2d, p2: Point2d): Point2d
    {
        Point2d(p1.x - p2.x, p1.y - p2.y)
    }
    
    function EuclideanDist(a: Point2d, b: Point2d): real
    {
        Sqrt(Square(a.x - b.x) + Square(a.y - b.y))
    }
    
    function ManhattanDist(a: Point2d, b: Point2d): real
    {
        abs(a.x - b.x) + abs(a.y - b.y)
    }
    
    lemma MulLtCompat(a: real, b: real, c: real)
        requires a < b
        requires c > 0.0
        ensures a * c < b * c
    {}
    
    lemma MulLtCompat4(a: real, b: real, c: real, d: real)
        requires 0.0 < a < b
        requires d > c > 0.0
        ensures a * c < b * d
    {
        assert a * c < b * d;
    }
    
    lemma SquareGtZero(x: real)
        ensures x > 0.0 ==> x * x > 0.0
    {
        if x > 0.0 {
            MulLtCompat(0.0, x, x);
        }
    }
    
    lemma SquareEqZero(x: real)
        requires x * x == 0.0
        ensures x == 0.0
    {
        if x > 0.0 {
            SquareGtZero(x);
        } else if x < 0.0 {
            var y := -x;
            assert x * x == y * y;
            SquareGtZero(y);
        }
    }
    
    lemma SquareLeInv(a: real, b: real)
        requires a >= 0.0 && b >= 0.0
        requires a * a <= b * b
        ensures a <= b
    {
        if b == 0.0 {
            SquareEqZero(a);
            return;
        }
    
        if b < a {
            MulLtCompat4(b, a, b, a);
            assert b * b < a * a;
        }
    }
    
    lemma EuclideanLeManhattan(a: Point2d, b: Point2d)
        ensures EuclideanDist(a, b) <= ManhattanDist(a, b)
    {
        SquareLeInv(Sqrt(Square(a.x - b.x) + Square(a.y - b.y)), abs(a.x - b.x) + abs(a.y - b.y));
    }
    
    
    lemma SquareSumDoubleSumSquare(x: real, y: real)
        requires x >= 0.0 && y >= 0.0
        ensures Square(x + y) <= 2.0 * (Square(x) + Square(y))
    {
        calc <==> {
            Square(x + y) <= 2.0 * (Square(x) + Square(y));
            Square(x) + Square(y) + 2.0 * x * y <= 2.0 * (Square(x) + Square(y));
            2.0 * x * y <= Square(x) + Square(y);
            0.0 <= Square(x) + Square(y) - 2.0 * x * y;
            0.0 <= Square(x - y);
            true;
        }
    }
    
    lemma ManhattanLeEuclidean(a: Point2d, b: Point2d)
        ensures ManhattanDist(a, b) <= EuclideanDist(a, b) * Sqrt(2.0)
    {
        var x := a.x - b.x;
        var y := a.y - b.y;
    
        calc <= {
               Square(abs(x) + abs(y));
            == Square(abs(x)) + Square(abs(y)) + 2.0 * abs(x) * abs(y);
            <= { SquareSumDoubleSumSquare(abs(x), abs(y)); }
               (Square(abs(x)) + Square(abs(y))) * 2.0;
            == Square(Sqrt((Square(x) + Square(y)) * 2.0));
            == Square(Sqrt(Square(x) + Square(y)) * Sqrt(2.0));
        }
        SquareLeInv(abs(x) + abs(y), Sqrt(Square(x) + Square(y)) * Sqrt(2.0));
    }

    predicate InBall(center: Point2d, r: real, x: Point2d)
    {
        ManhattanDist(center, x) < r
    }
    
    function Ball(center: Point2d, r: real): iset<Point2d>
    {
        iset x | InBall(center, r, x)
    }

    predicate InInterior(x: Point2d, S: iset<Point2d>)
    {
        exists eps | eps > 0.0 :: Ball(x, eps) <= S
    }
    
    function Interior(S: iset<Point2d>): iset<Point2d>
    {
        iset x | InInterior(x, S)
    }
    
    predicate Open(S: iset<Point2d>)
    {
        forall x | x in S :: InInterior(x, S)
    }

    predicate InClosure(x: Point2d, S: iset<Point2d>)
    {
        forall eps | eps > 0.0 :: !(Ball(x, eps) !! S)
    }
    
    function Closure(S: iset<Point2d>): iset<Point2d>
    {
        iset x | InClosure(x, S)
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
    
    lemma HullSetBounded(S: iset<real>)
        requires Bounded(S)
        ensures Bounded(HullSet(S))
    {
        var lb, ub :| IsLB(lb, S) && IsUB(ub, S);

        assert IsLB(lb, HullSet(S));
        assert IsUB(ub, HullSet(S));
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

    lemma BoundedSubset(A: iset<real>, B: iset<real>)
        requires A <= B && Bounded(B)
        ensures Bounded(A)
    {
        var l :| IsLB(l, B);
        var u :| IsUB(u, B);

        assert IsLB(l, A);
        assert IsUB(u, A);
    }

    lemma InteriorBounded(S: iset<real>)
        requires Bounded(S)
        ensures Bounded(Interior(S))
    {
        InteriorSubset(S);
        BoundedSubset(Interior(S), S);
    }

    lemma ClosureBounded(S: iset<real>)
        requires Bounded(S)
        ensures Bounded(Closure(S))
    {
        var l :| IsLB(l, S);
        var u :| IsUB(u, S);

        forall x | x in Closure(S)
            ensures l <= x && x <= u
        {
            forall eps | eps > 0.0
                ensures LEModuloEpsilon(l, x, eps)
            {
                assert !(Ball(x, eps) !! S);
                var y :| y in S && y in Ball(x, eps);
                assert l <= y;
            }
            EstablishLE(l, x);

            forall eps | eps > 0.0
                ensures LEModuloEpsilon(x, u, eps)
            {
                assert !(Ball(x, eps) !! S);
                var y :| y in S && y in Ball(x, eps);
                assert y <= u;
            }
            EstablishLE(x, u);
        }
        assert IsLB(l, Closure(S));
        assert IsUB(u, Closure(S));
    }

    lemma RegularJoinBounded(A: iset<real>, B: iset<real>)
        requires Bounded(A) && Bounded(B)
        ensures Bounded(RegularJoin(A, B))
    {
        UnionBounded(A, B);
        ClosureBounded(A + B);
        InteriorBounded(Closure(A + B));
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
        | Hull(e: Expr)
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
    function Denote(e: Expr): (S: iset<real>)
        ensures Bounded(S)
    {
        match e
            case Empty =>
                EmptyBounded();
                iset{}
            case Unit =>
                OpenIntervalBounded(0.0, 1.0);
                OpenInterval(0.0, 1.0)
            case Hull(e) =>
                HullSetBounded(Denote(e));
                HullSet(Denote(e))
            case Translate(r,e) =>
                TranslateSetBounded(r, Denote(e));
                TranslateSet(r, Denote(e))
            case Home(r, e) => var S' := Denote(e);
                TranslateSetBounded(-RelPos(r, S'), S');
                TranslateSet(-RelPos(r, S'), S')
            case Scale(r,e) =>
                ScaleSetBounded(r, Denote(e));
                ScaleSet(r, Denote(e))
            case Intersect(e1,e2) =>
                IntersectBounded(Denote(e1), Denote(e2));
                Denote(e1) * Denote(e2)
            case Union(e1,e2) =>
                RegularJoinBounded(Denote(e1), Denote(e2));
                RegularJoin(Denote(e1), Denote(e2))
            case Difference(e1,e2) =>
                DifferenceBounded(Denote(e1), Closure(Denote(e2)));
                Denote(e1) - Closure(Denote(e2))
    }


    lemma UnionUnitTest()
        ensures Denote(Union(Unit, Translate(1.0, Unit))) == Denote(Scale(2.0, Unit))
    {
        calc {
            Denote(Union(Unit, Translate(1.0, Unit)));
            RegularJoin(OpenInterval(0.0, 1.0), TranslateSet(1.0, OpenInterval(0.0, 1.0)));
            Interior(Closure(OpenInterval(0.0, 1.0) + OpenInterval(1.0, 2.0)));
            { CloseAdjacentOpenIntervals(0.0, 1.0, 2.0); }
            Interior(Closure(OpenInterval(0.0, 2.0)));
            { ClosureOpenInterval(0.0, 2.0); }
            Interior(ClosedInterval(0.0, 2.0));
            { InteriorClosedInterval(0.0, 2.0); }
            OpenInterval(0.0, 2.0);
            Denote(Scale(2.0, Unit));
        }
    }
    
    lemma DiffUnitTest()
        ensures Denote(Difference(Unit, Translate(1.0, Unit))) == Denote(Unit)
    {
        calc {
            Denote(Difference(Unit, Translate(1.0, Unit)));
            OpenInterval(0.0, 1.0) - Closure(OpenInterval(1.0, 2.0));
            { ClosureOpenInterval(1.0, 2.0); }
            OpenInterval(0.0, 1.0) - ClosedInterval(1.0, 2.0);
            Denote(Unit);
        }
    }
    
    // Look ma, no proof!
    lemma IntersectUnitTest()
        ensures Denote(Intersect(Unit, Translate(1.0, Unit))) == Denote(Empty)
    {}
    
    lemma DenoteRegularOpen(e: Expr)
        ensures RegularOpen(Denote(e))
    {
        match e {
            case Empty => RegularOpenEmpty();
            case Unit => OpenIntervalRegularOpen(0.0, 1.0);
            case Hull(e) => HullSetRegularOpen(Denote(e));
            case Translate(r, e) => TranslateSetRegularOpen(r, Denote(e));
            case Home(r, e) => var S := Denote(e);
                TranslateSetRegularOpen(-RelPos(r, S), S);
            case Scale(r, e) => ScaleSetRegularOpen(r, Denote(e));
            case Intersect(e1, e2) => IntersectRegularOpen(Denote(e1), Denote(e2));
            case Union(e1, e2) => RegularJoinRegularOpen(Denote(e1), Denote(e2));
            case Difference(e1, e2) => DifferenceRegularOpen(Denote(e1), Denote(e2));
        }
    }

    lemma DenoteRegularizableOpen(e: Expr)
        ensures RegularizableOpen(Denote(e))
    {
        DenoteRegularOpen(e);
        RegularOpenRegular(Denote(e));
        RegularOpenOpen(Denote(e));
    }


    lemma DenoteOpen(e: Expr)
        ensures Open(Denote(e))
    {
        DenoteRegularOpen(e);
        RegularOpenOpen(Denote(e));
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
            assert !(Denote(e) !! Ball(x, eps / 2.0));
            var y :| y in Denote(e) && y in Ball(x, eps / 2.0);
            if x == y {
                DenoteOpen(e);
                assert InInterior(y, Denote(e));
                var eps' :| eps' > 0.0 && Ball(y, eps') <= Denote(e);
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
            assert x in Closure(Denote(e));
            var x' :| x' in Ball(x, eps) && x' in Denote(e);
            DenoteOpen(e);
            var eps' :| eps' > 0.0 && Ball(x', eps') <= Denote(e);
    
            var eps'' := min(eps', eps - abs(x - x'));
            assert Ball(x', eps'') <= Denote(e);
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
    {
        var S := Denote(e);
        calc {
            Denote(Union(e, e));
            RegularJoin(S, S);
            Interior(Closure(S + S));
            { assert S == S + S; }
            Interior(Closure(S));
            { DenoteRegularOpen(e); }
            S;
        }
    }
    
    lemma SelfIntersect(e: Expr)
        ensures Equiv(Intersect(e, e), e)
    {}
    
    lemma SelfDifference(e: Expr)
        ensures Equiv(Difference(e, e), Empty)
    {}
    
    lemma UnionEmpty(e: Expr)
        ensures Equiv(Union(e, Empty), e)
    {
        var S := Denote(e);
        calc {
            Denote(Union(e, Empty));
            RegularJoin(S, iset{});
            Interior(Closure(S + iset{}));
            { assert S == S + iset{}; }
            Interior(Closure(S));
            { DenoteRegularOpen(e); }
            S;
        }
    }
    
    lemma IntersectEmpty(e: Expr)
        ensures Equiv(Intersect(e, Empty), Empty)
    {}
    
    
    lemma DifferenceEmpty1(e: Expr)
        ensures Equiv(Difference(e, Empty), e)
    {
        calc {
            Denote(Difference(e, Empty));
            Denote(e) - Closure(iset{});
            { ClosureEmpty(); }
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
        forall e { DenoteRegularizableOpen(e); }
        RegularJoinAssoc(Denote(e1), Denote(e2), Denote(e3));
    }
    
    lemma IntersectAssoc(e1: Expr, e2: Expr, e3: Expr)
        ensures Equiv(Intersect(e1, Intersect(e2, e3)), Intersect(Intersect(e1, e2), e3))
    {
        assert
            Denote(e1) * (Denote(e2) * Denote(e3)) ==
            (Denote(e1) * Denote(e2)) * Denote(e3);
    }
    
    lemma IntersectDifference'(A: iset<real>, B: iset<real>)
        requires Open(A) && Open(B) && Regular(B)
        ensures A * B == A - Closure(A - Closure(B))
    {
        IntersectOpen(A, B);

        forall x | x in A && x !in Closure(A - Closure(B))
            ensures x in B
        {
            var eps :| eps > 0.0 && (Ball(x, eps) !! (A - Closure(B)));
            var eps' :| eps' > 0.0 && Ball(x, eps') <= A;
            var eps'' := min(eps, eps');

            forall y | y in Ball(x, eps'')
                ensures y in Closure(B)
            {
                assert y in Ball(x, eps) && y in A;
            }
            assert Ball(x, eps'') <= Closure(B);
            assert x in Interior(Closure(B));
            assert x in B;
        }
    }


    lemma IntersectDifference(e1: Expr, e2: Expr)
        ensures Equiv(Intersect(e1, e2), Difference(e1, Difference(e1, e2)));
    {
        DenoteRegularOpen(e1);
        DenoteRegularOpen(e2);
        RegularOpenIffRegularAndOpen(Denote(e1));
        RegularOpenIffRegularAndOpen(Denote(e2));
        IntersectDifference'(Denote(e1), Denote(e2));
    }
}

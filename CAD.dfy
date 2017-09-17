// RUN: /compile:0 /rlimit:500000

datatype Expr =
    | Empty
    | Unit
    | Translate(r: real, e: Expr)
    | Scale(r: real, e: Expr)
    | Home(r: real, e: Expr)
    | Intersect(e1: Expr, e2: Expr)
    | Union(e1: Expr, e2: Expr)
    | Difference(e1: Expr, e2: Expr)

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

function DenoteTranslate(r: real, S: iset<real>): iset<real>
{
    iset x {:nowarn} | x - r in S
}


function DenoteScale(r: real, S: iset<real>): iset<real>
{
    if r == 0.0 then iset{}
    else iset x {:nowarn} | x / r in S
}


// The following example shows that the semantics of difference cannot
// be A - B, but must be A - cl(B)

function HalfOpenInterval(): iset<real>
{
    OpenInterval(-0.5, 0.5) - OpenInterval(0.0, 0.5)
}

// Construct the singleton set containing 0.0
lemma Bad()
    ensures forall x | x in HalfOpenInterval() && x in DenoteScale(-1.0, HalfOpenInterval()) :: x == 0.0
{}


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

lemma DenoteTranslateBounded(r: real, S: iset<real>)
    requires Bounded(S)
    ensures Bounded(DenoteTranslate(r, S))
{
    var a :| IsLB(a, S);
    var b :| IsUB(b, S);
    assert IsLB(a + r, DenoteTranslate(r, S));
    assert IsUB(b + r, DenoteTranslate(r, S));
}

lemma DenoteScaleBounded(r: real, S: iset<real>)
    requires Bounded(S)
    ensures Bounded(DenoteScale(r, S))
{
    var a :| IsLB(a, S);
    var b :| IsUB(b, S);
    if r == 0.0 {
        EmptyBounded();
    } else if r > 0.0 {
        assert IsLB(a * r, DenoteScale(r, S));
        assert IsUB(b * r, DenoteScale(r, S));
    } else {
        assert IsLB(b * r, DenoteScale(r, S));
        assert IsUB(a * r, DenoteScale(r, S));
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
            DenoteTranslateBounded(r, OpenDenote(e));
            DenoteTranslate(r, OpenDenote(e))
        case Home(r, e) => var S' := OpenDenote(e);
            if S' == iset{} then
                EmptyBounded();
                iset{}
            else
                DenoteTranslateBounded(RelPos(r, S'), S');
                DenoteTranslate(RelPos(r, S'), S')
        case Scale(r,e) =>
            DenoteScaleBounded(r, OpenDenote(e));
            DenoteScale(r, OpenDenote(e))
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

// ⟦e⟧
function Denote(e: Expr): iset<real>
{
    Closure(OpenDenote(e))
}

lemma ISetNonEmpty<A>(x: A, S: iset<A>)
    requires x in S
    ensures S != iset{}
{}

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

lemma UnionUnitTest()
    ensures Denote(Union(Unit, Translate(1.0, Unit))) == Denote(Scale(2.0, Unit))
{
    calc {
        Denote(Union(Unit, Translate(1.0, Unit)));
        == Closure(OpenDenote(Union(Unit, Translate(1.0, Unit))));
        == Closure(OpenInterval(0.0, 1.0) + DenoteTranslate(1.0, OpenInterval(0.0, 1.0)));
        == Closure(OpenInterval(0.0, 1.0) + OpenInterval(1.0, 2.0));
        == { CloseAdjacentOpenIntervals(0.0, 1.0, 2.0); }
           Closure(OpenInterval(0.0, 2.0));
        == Closure(DenoteScale(2.0, OpenInterval(0.0, 1.0)));
        == Closure(OpenDenote(Scale(2.0, Unit)));
        == Denote(Scale(2.0, Unit));
    }
}

lemma DiffUnitTest()
    ensures Denote(Difference(Unit, Translate(1.0, Unit))) == Denote(Unit)
{
    calc {
        Denote(Difference(Unit, Translate(1.0, Unit)));
        Closure(OpenInterval(0.0, 1.0) - Closure(DenoteTranslate(1.0, OpenInterval(0.0, 1.0))));
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

lemma DenoteTranslateOpen(r: real, S: iset<real>)
    requires Open(S)
    ensures Open(DenoteTranslate(r, S))
{
    var S' := DenoteTranslate(r, S);
    forall x | x in S'
        ensures exists eps | eps > 0.0 :: Ball(x, eps) <= S'
    {
        var y := x - r;
        assert y in S;
        var eps :| eps > 0.0 && Ball(y, eps) <= S;

        assert Ball(x, eps) <= S';
    }
}

lemma DenoteScaleOpen(r: real, S: iset<real>)
    requires Open(S)
    ensures Open(DenoteScale(r, S))
{
    if r == 0.0 { return; }
    var S' := DenoteScale(r, S);
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


lemma OpenDenoteOpen(e: Expr)
    ensures Open(OpenDenote(e))
{
    match e {
        case Empty =>
        case Unit => OpenIntervalOpen(0.0, 1.0);
        case Translate(r, e) => DenoteTranslateOpen(r, OpenDenote(e));
        case Home(r, e) => var S := OpenDenote(e);
            if S != iset{} {
                DenoteTranslateOpen(RelPos(r, S), S);
            }
        case Scale(r, e) => { DenoteScaleOpen(r, OpenDenote(e)); }
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

predicate Bounded(S: iset<real>)
{
    && (exists x :: IsLB(x, S))
    && (exists x :: IsUB(x, S))
}

predicate NonEmpty(S: iset<real>)
{
    exists x :: x in S
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

function RelPos(r: real, S: iset<real>): real
    requires NonEmpty(S) && Bounded(S)
{
    var (a, b) := BBox(S);
    a + r * (b - a)
}




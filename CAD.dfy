// RUN: /rlimit:500000

datatype Expr =
    | Empty
    | Unit
    | Translate(r: real, e: Expr)
    | Scale(r: real, e: Expr)
    /*| Home(r: real, e: Expr)*/
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
    iset x | x in S :: r + x
}


function DenoteScale(r: real, S: iset<real>): iset<real>
{
    iset x | x in S :: r * x
}

function OpenDenote(e: Expr): iset<real>
{
    match e
        case Empty => iset{}
        case Unit => OpenInterval(0.0, 1.0)
        case Translate(r,e) => DenoteTranslate(r, OpenDenote(e))
        case Scale(r,e) => DenoteScale(r, OpenDenote(e))
        case Intersect(e1,e2) => OpenDenote(e1) * OpenDenote(e2)
        case Union(e1,e2) => OpenDenote(e1) + OpenDenote(e2)
        case Difference(e1,e2) => OpenDenote(e1) - OpenDenote(e2)
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
    abs(center - x) <= r
}

function Ball(center: real, r: real): iset<real>
{
    iset x | InBall(center, r, x)
}

predicate InClosure(S: iset<real>, x: real)
{
    forall eps | eps > 0.0 :: Ball(x, eps) * S != iset{}
}

function Closure(S: iset<real>): iset<real>
{
    iset x | InClosure(S, x)
}

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
            assert x in ClosedInterval(a, b);
        } else if x > b {
            var eps := (x - b) / 2.0;
            var y :| y in Ball(x, eps) * OpenInterval(a, b);
            assert x in ClosedInterval(a, b);
        } else {
            assert x in ClosedInterval(a, b);
        }
    }

    forall x | x in ClosedInterval(a, b)
        ensures x in Closure(OpenInterval(a, b))
    {
        if x == a {
            forall eps | eps > 0.0
                ensures Ball(a, eps) * OpenInterval(a, b) != iset{}
            {
                var d := min(eps, (b - a) / 2.0);
                ISetNonEmpty(x + d, Ball(a, eps) * OpenInterval(a, b));
            }

            assert x in Closure(OpenInterval(a, b));
        } else if x == b {
            forall eps | eps > 0.0
                ensures Ball(b, eps) * OpenInterval(a, b) != iset{}
            {
                var d := min(eps, (b - a) / 2.0);
                ISetNonEmpty(x - d, Ball(b, eps) * OpenInterval(a, b));
            }

            assert x in Closure(OpenInterval(a, b));
        } else {
            forall eps | eps >= 0.0
                ensures Ball(x, eps) * OpenInterval(a, b) != iset{}
            {
                ISetNonEmpty(x, Ball(x, eps) * OpenInterval(a, b));
            }

            assert x in Closure(OpenInterval(a, b));
        }
    }
}

lemma TranslateOpenInterval(r: real, a: real, b: real)
    ensures DenoteTranslate(r, OpenInterval(a, b)) == OpenInterval(r + a, r + b)
{
    forall x: real
        ensures x in DenoteTranslate(r, OpenInterval(a, b)) <==> x in OpenInterval(r + a, r + b)
    {
        calc {
            x in DenoteTranslate(r, OpenInterval(a, b));
            <==> x in (iset y | y in OpenInterval(a, b) :: r + y);
            <==> {
                if r + a < x < r + b {
                    assert x - r in OpenInterval(a, b);
                }
            } r + a < x < r + b;
            <==> x in OpenInterval(r + a, r + b);
        }

    }
}

lemma ScaleOpenInterval(r: real, a: real, b: real)
    requires r > 0.0
    ensures DenoteScale(r, OpenInterval(a, b)) == OpenInterval(r * a, r * b)
{
    forall x: real
        ensures x in DenoteScale(r, OpenInterval(a, b)) <==> x in OpenInterval(r * a, r * b)
    {
        calc {
            x in DenoteScale(r, OpenInterval(a, b));
            <==> x in (iset y | y in OpenInterval(a, b) :: r * y);
            <==> {
                if r * a < x < r * b {
                    var y := x / r;
                    assert y in OpenInterval(a, b);
                    assert r * y == x;
                }
            } r * a < x < r * b;
            <==> x in OpenInterval(r * a, r * b);
        }

    }
}

lemma CloseAdjacentOpenIntervals(a: real, b: real, c: real)
    requires a <= b <= c
    ensures Closure(OpenInterval(a, b) + OpenInterval(b, c)) == Closure(OpenInterval(a, c))
{
    if a == b || b == c { return; }
    ClosureOpenInterval(a, c);
    var S := OpenInterval(a, b) + OpenInterval(b, c);
    forall x | x in ClosedInterval(a, c)
        ensures x in Closure(S);
    {
        forall eps | eps > 0.0
            ensures Ball(x, eps) * S != iset{}
        {
            if x == a {
                ISetNonEmpty(x + min(eps, (b - a)) / 2.0, Ball(x, eps) * S);
                assert Ball(x, eps) * S != iset{};
            } else if x == b {
                ISetNonEmpty(x - min(eps, (b - a)) / 2.0, Ball(x, eps) * S);
                assert Ball(x, eps) * S != iset{};
            } else if x == c {
                ISetNonEmpty(x - min(eps, (c - b)) / 2.0, Ball(x, eps) * S);
                assert Ball(x, eps) * S != iset{};
            } else {
                ISetNonEmpty(x, Ball(x, eps) * S);
            }
        }
    }
}

lemma UnionUnitTest()
    ensures Denote(Union(Unit, Translate(1.0, Unit))) == Denote(Scale(2.0, Unit))
{
    calc {
        Denote(Union(Unit, Translate(1.0, Unit)));
        == Closure(OpenDenote(Union(Unit, Translate(1.0, Unit)))); 
        == {
            calc {
                OpenDenote(Union(Unit, Translate(1.0, Unit)));
                == OpenInterval(0.0, 1.0) + DenoteTranslate(1.0, OpenInterval(0.0, 1.0));
                == { TranslateOpenInterval(1.0, 0.0, 1.0); }
                   OpenInterval(0.0, 1.0) + OpenInterval(1.0, 2.0);
            }
        }
        Closure(OpenInterval(0.0, 1.0) + OpenInterval(1.0, 2.0));
        == { CloseAdjacentOpenIntervals(0.0, 1.0, 2.0); }
           Closure(OpenInterval(0.0, 2.0));
        == { ScaleOpenInterval(2.0, 0.0, 1.0); }
           Closure(DenoteScale(2.0, OpenInterval(0.0, 1.0)));
        == Closure(OpenDenote(Scale(2.0, Unit)));
        == Denote(Scale(2.0, Unit));
    }
}

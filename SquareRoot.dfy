// RUN: /compile:0

function Sqrt(x: real): (y: real)
    requires x >= 0.0
    ensures y >= 0.0 && y * y == x

lemma MulLtCompat(a: real, b: real, c: real)
    requires a < b
    requires c > 0.0
    ensures a * c < b * c
{}

lemma SquareGtZero(x: real)
    ensures x > 0.0 ==> x * x > 0.0
{
    if x > 0.0 {
        MulLtCompat(0.0, x, x);
    }
}

lemma SquareEqZero(x: real)
    ensures x * x == 0.0 ==> x == 0.0
{
    if x * x == 0.0 {
        if x > 0.0 {
            SquareGtZero(x);
        } else if x < 0.0 {
            var y := -x;
            assert x * x == y * y;
            SquareGtZero(y);
        }
    }
}

lemma SqrtZero()
    ensures Sqrt(0.0) == 0.0
{
    var x := Sqrt(0.0);
    assert x * x == 0.0;
    SquareGtZero(x);
}

datatype Point2d = Point2d(x: real, y: real)

function Norm(p: Point2d): real
{
    var Point2d(x, y) := p;
    Sqrt(x * x + y * y)
}

lemma NormZeroIffZero(p: Point2d)
    ensures Norm(p) == 0.0 <==> p == Point2d(0.0, 0.0)
{
    var Point2d(x, y) := p;

    if Norm(p) == 0.0 {
        SquareEqZero(x);
        SquareEqZero(y);
        assert p == Point2d(0.0, 0.0);
    }

    if p == Point2d(0.0, 0.0) {
        SqrtZero();
        assert Norm(p) == 0.0;
    }
}

function Subtract(p1: Point2d, p2: Point2d): Point2d
{
    Point2d(p1.x - p2.x, p1.y - p2.y)
}

function Dist(p1: Point2d, p2: Point2d): real
{
    Norm(Subtract(p1, p2))
}

lemma DistZeroIffEq(p1: Point2d, p2: Point2d)
    ensures Dist(p1, p2) == 0.0 <==> p1 == p2
{
    NormZeroIffZero(Subtract(p1, p2));
}

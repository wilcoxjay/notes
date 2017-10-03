// RUN: /compile:0 /rlimit:500000 /vcsCores:4

function Abs(r: real): (y: real)
{
    if r < 0.0 then
        - r
    else r
}

datatype Point2d = Point2d(x: real, y: real)

function Sqrt(x: real): (y: real)
    requires x >= 0.0
    ensures y >= 0.0 && y * y == x

function Square(x: real): (y: real)
    ensures y >= 0.0
{
    x * x
}

function EuclideanDist(a: Point2d, b: Point2d): real
{
    Sqrt(Square(a.x - b.x) + Square(a.y - b.y))
}

function ManhattanDist(a: Point2d, b: Point2d): real
{
    Abs(a.x - b.x) + Abs(a.y - b.y)
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
{}

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
    SquareLeInv(Sqrt(Square(a.x - b.x) + Square(a.y - b.y)), Abs(a.x - b.x) + Abs(a.y - b.y));
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
           Square(Abs(x) + Abs(y));
        == Square(Abs(x)) + Square(Abs(y)) + 2.0 * Abs(x) * Abs(y);
        <= { SquareSumDoubleSumSquare(Abs(x), Abs(y)); }
           (Square(Abs(x)) + Square(Abs(y))) * 2.0;
        == Square(Sqrt((Square(x) + Square(y)) * 2.0));
        == Square(Sqrt(Square(x) + Square(y)) * Sqrt(2.0));
    }
    SquareLeInv(Abs(x) + Abs(y), Sqrt(Square(x) + Square(y)) * Sqrt(2.0));
}

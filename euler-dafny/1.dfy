// RUN: /compile:3 /noNLarith

module Attempt1 {

function PickForSum(s: set<int>): (x:int)
    requires s != {}
    ensures x in s
{
    var x :| x in s;
    x
}

function Sum(s: set<int>): int
{
    if s == {} then
        0
    else
        var x := PickForSum(s);
        x + Sum(s - {x})
}

lemma SumDecompose(s: set<int>, y: int)
    requires y in s
    ensures Sum(s) == y + Sum(s - {y})
    decreases s
{
    if s != {} {
        var x := PickForSum(s);
        if x != y {
            calc {
                Sum(s);
                == x + Sum(s - {x});
                == { SumDecompose(s - {x}, y); }
                   x + (y + Sum((s - {x}) - {y}));
                == { assert (s - {x}) - {y} == (s - {y}) - {x}; }
                   y + (x + Sum((s - {y}) - {x}));
                == { SumDecompose(s - {y}, x); }
                   y + Sum(s - {y});
            }
        }
    }
}

function MultiplesOfThreeAndFiveUpTo(n: nat): set<nat>
{
  set x | 0 <= x < n && (x % 3 == 0 || x % 5 == 0)
}

method SumOfMultiplesOfThreeAndFive(N: nat) returns(sum: nat)
{
    var n := 0;
    sum := 0;
    while n < N
        invariant sum == Sum(MultiplesOfThreeAndFiveUpTo(n))
    {
        if n % 3 == 0 || n % 5 == 0 {
            sum := sum + n;
            SumDecompose(MultiplesOfThreeAndFiveUpTo(n+1), n);
            assert MultiplesOfThreeAndFiveUpTo(n+1) == MultiplesOfThreeAndFiveUpTo(n) + {n};
        } else {
            assert MultiplesOfThreeAndFiveUpTo(n+1) == MultiplesOfThreeAndFiveUpTo(n);
        }

        n := n + 1;
    }
}

}

module Attempt2 {
function Spec(n: nat): nat
{
    if n == 0 then
        0
    else if n % 3 == 0 || n % 5 == 0 then
        Spec(n - 1) + n
    else
        Spec(n - 1)
}

function Inv(n: nat, i: nat, acc: nat): nat
    requires i <= n
    decreases n - i
{
    if i >= n then
        acc
    else if i % 3 == 0 || i % 5 == 0 then
        Inv(n, i + 1, acc + i)
    else
        Inv(n, i + 1, acc)
}

lemma SpecInv(n: nat, i: nat, acc: nat)
    requires i <= n
    ensures Spec(n) == Inv(n + 1, i, Spec(i))
{
}

method SumOfMultiplesOfThreeAndFive(n: nat) returns(sum: nat)
{
    var i := 0;
    sum := 0;
    while i < n
        invariant 0 <= i <= n
        invariant Inv(n, 0, 0) == Inv(n, i, sum)
    {
        if i % 3 == 0 || i % 5 == 0 {
            sum := sum + i;
        }

        i := i + 1;
    }
}

}

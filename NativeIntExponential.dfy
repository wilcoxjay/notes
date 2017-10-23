// RUN: /compile:0

newtype {:nativeType "uint"} u32 =
  x: int | 0 <= x < 0x100000000

function pow2(n: nat): int
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma {:fuel pow2,31,32} {:induction false} pow2Bounds(n: nat)
    requires n < 32
    ensures 0 <= pow2(n) < 0x100000000
{
}


function pow2u32(n: u32): u32
    requires n < 32
{
    pow2Bounds(n as nat);
    pow2(n as nat) as u32
}


/*lemma pow2Monotone(a: nat, b: nat)
    requires a < b
    ensures pow2(a) < pow2(b)
{}

lemma pow2unroll2(n: nat)
    requires n >= 2
    ensures pow2(n) == 4 * pow2(n - 2)
{}

lemma pow2unroll4(n: nat)
    requires n >= 4
    ensures pow2(n) == 0x10 * pow2(n - 4)
{
    pow2unroll2(n);
    pow2unroll2(n-2);
}

lemma pow2unroll8(n: nat)
    requires n >= 8
    ensures pow2(n) == 0x100 * pow2(n - 8)
{
    pow2unroll4(n);
    pow2unroll4(n-4);
}

lemma pow2unroll16(n: nat)
    requires n >= 16
    ensures pow2(n) == 0x10000 * pow2(n - 16)
{
    pow2unroll8(n);
    pow2unroll8(n-8);
}


lemma pow2Bounds(n: nat)
    requires n < 32
    ensures 0 <= pow2(n) < 0x100000000
{
    var k := n;
    if k >= 16 {
        pow2unroll16(k);
        k := k - 16;
    }
    if k >= 8 {
        pow2unroll8(k);
        k := k - 8;
    }
    if k >= 4 {
        pow2unroll4(k);
        k := k - 4;
    }
    if k >= 2 {
        pow2unroll2(k);
        k := k - 2;
    }
}

lemma pow2Bounds'(n: nat)
    requires n < 32
    ensures 0 <= pow2(n) < 0x100000000
{
    if n == 0 {
    } else if n ==  1 {
    } else if n ==  2 {
    } else if n ==  3 {
    } else if n ==  4 {
    } else if n ==  5 {
    } else if n ==  6 {
    } else if n ==  7 {
    } else if n ==  8 {
    } else if n ==  9 {
    } else if n == 10 {
    } else if n == 11 {
    } else if n == 12 {
    } else if n == 13 {
    } else if n == 14 {
    } else if n == 15 {
    } else if n == 16 {
    } else if n == 17 {
    } else if n == 18 {
    } else if n == 19 {
    } else if n == 20 {
    } else if n == 21 {
    } else if n == 22 {
    } else if n == 23 {
    } else if n == 24 {
    } else if n == 25 {
    } else if n == 26 {
    } else if n == 27 {
    } else if n == 28 {
    } else if n == 29 {
    } else if n == 30 {
    } else if n == 31 {
    }
}

lemma pow2Bounds''(n: nat)
    requires n < 32
    ensures 0 <= pow2(n) < 0x100000000
{
    if n ==  2 {
    } else if n ==  4 {
    } else if n ==  6 {
    } else if n ==  8 {
    } else if n == 10 {
    } else if n == 12 {
    } else if n == 14 {
    } else if n == 16 {
    } else if n == 18 {
    } else if n == 20 {
    } else if n == 22 {
    } else if n == 24 {
    } else if n == 26 {
    } else if n == 28 {
    } else if n == 30 {
    }
}

lemma pow2Bounds'''(n: nat)
    requires n < 32
    ensures 0 <= pow2(n) < 0x100000000
{
    pow2Monotone(n, 32);
}
*/

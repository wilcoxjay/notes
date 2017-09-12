// RUN: /compile:0 /nologo

function G(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else a[0] + G(a[1..])
}

method sum(a: seq<int>) returns (r: int)
  ensures r == G(a)
{
  r := 0;
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant r == G(a[0..i])
  {
    calc {
           r + a[i];
        == G(a[0..i]) + a[i];
        == { G_append(a[0..i], [a[i]]); }
           G(a[0..i] + [a[i]]);
        == { assert a[0..i+1] == a[0..i] + [a[i]]; }
           G(a[0..i+1]);
    }

    r := r + a[i];
    i := i + 1;
  }

  assert a == a[..|a|];
}

lemma G_append(a: seq<int>, b: seq<int>)
    ensures G(a + b) == G(a) + G(b)
{
    if a != [] {
        calc {
               G(a + b);
            == (a + b)[0] + G((a + b)[1..]);
            == a[0] + G((a + b)[1..]);
            == { assert (a + b)[1..] == a[1..] + b; }
               a[0] + G(a[1..] + b);
            == G(a) + G(b);
        }
    }
}

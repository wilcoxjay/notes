lemma Plus_Assoc<A>(xs: seq<A>, ys: seq<A>, zs: seq<A>)
  ensures (xs + ys) + zs == xs + (ys + zs)
{}

function method Map<A, B>(f: A -> B, l: seq<A>): seq<B>
  reads f.reads
  requires forall x :: f.requires(x)
{
  if l == [] then
    []
  else
    [f(l[0])] + Map(f, l[1..])
}

lemma MapLength<A, B>(f: A -> B, l: seq<A>)
  requires forall x :: f.requires(x)
  ensures |Map(f, l)| == |l|
{}

lemma MapIndex<A, B>(f: A -> B, l: seq<A>)
  requires forall x :: f.requires(x)
  ensures forall i :: 0 <= i < |l| ==>
    (MapLength(f, l);
     Map(f, l)[i] == f(l[i]))
{
}

lemma Map_Plus<A, B>(f: A -> B, l1: seq<A>, l2: seq<A>)
  requires forall x :: f.requires(x)
  ensures Map(f, l1 + l2) == Map(f, l1) + Map(f, l2)
{
  if l1 != [] {
    assert (l1 + l2)[1..] == l1[1..] + l2;
  }
}

class C {
  var x: int
}

function method Seq(a: int, n: nat): seq<int>
  decreases n
{
  if n == 0 then
    []
  else
    [a] + Seq(a + 1, n - 1)
}

lemma SeqLength(a: int, n: nat)
  decreases n
  ensures |Seq(a, n)| == n
{}

method IncAll(l: seq<int>) returns (l': seq<int>)
  ensures |l'| == |l|
  ensures forall i :: 0 <= i < |l| ==> l'[i] == l[i] + 1
{
  var c := new C;
  c.x := 1;
  var f := (z: int) reads c => z + c.x;
  l' := Map(f, l);
  MapLength(f, l);
  MapIndex(f, l);
}

lemma SeqExt<A>(l1: seq<A>, l2: seq<A>)
  requires |l1| == |l2|
  requires forall i :: 0 <= i < |l1| ==> l1[i] == l2[i]
  ensures l1 == l2
{}

lemma SeqIndex(a: int, n: nat)
  decreases n
  ensures (SeqLength(a, n);
           forall i :: 0 <= i < n ==> Seq(a, n)[i] == a + i)
{}

method Main(n: nat)
{
  var l := Seq(0, n);
  l := IncAll(l);
  SeqIndex(0, n);
  SeqIndex(1, n);
  SeqLength(0, n);
  SeqLength(1, n);
  SeqExt(l, Seq(1, n));
  assert l == Seq(1, n);
}

// hashtag demo

// - binary search
// - insertion sort
// - partition/dutch national flag/331 hw0




// given array of integers
// reorder array such that all the negatives come first
// then all the zeroes, and then all the positives



method Partition(a: array<int>) returns (lo: int, hi: int)
  // postcondition: 
  // in a, all the negatives come first
  // then all the zeroes, and then all the positives
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall i | 0 <= i < lo :: a[i] < 0
  ensures forall i | lo <= i < hi :: a[i] == 0
  ensures forall i | hi <= i < a.Length :: a[i] > 0
{
  var i := 0;
  var j := a.Length;
  var k := a.Length;

  while i < j
    invariant 0 <= i <= j <= k <= a.Length
    invariant forall m | 0 <= m < i :: a[m] < 0
    invariant forall m | j <= m < k :: a[m] == 0
    invariant forall m | k <= m < a.Length :: a[m] > 0
  {
    if a[i] < 0 {
      i := i + 1;
    } else if a[i] == 0 {
      var current := a[i];
      a[i] := a[j-1];
      a[j-1] := current;
      j := j - 1;
    } else {
      assert a[i] > 0;
      var current := a[i];
      a[i] := a[j-1];
      a[j-1] := a[k-1];
      a[k-1] := current;
      j := j - 1;
      k := k - 1;
    }
  }
  return i, k;
}





method Main()
{
  var x := 3;

  assert x < 7;
}

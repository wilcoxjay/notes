method Allocate<T(0)>(n: int) returns (a: array<T>)
    requires n >= 0
    ensures a != null && a.Length == n && fresh(a)
{
    a := new T[n];
}

method Main()
{
    var a := Allocate<int>(10);
    a[0] := 0;
}

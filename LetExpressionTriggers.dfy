// RUN: /compile:0

predicate Foo(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> var j := i; s[j] > 0
}

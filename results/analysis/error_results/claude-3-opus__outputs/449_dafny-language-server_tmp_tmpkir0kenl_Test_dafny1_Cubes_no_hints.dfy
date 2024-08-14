// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Cubes(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == i*i*i
{
  var n := 0;
  var c := 0;
  var k := 1;
  var m := 6;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant c == n*n*n
    invariant k == 3*n*n + 3*n + 1
    invariant m == 6*n + 6
    invariant forall i :: 0 <= i < n ==> a[i] == i*i*i
  {
    a[n] := c;
    n := n + 1;
    m := m + 6;
    k := k + m;
    c := c + k;
  }
}
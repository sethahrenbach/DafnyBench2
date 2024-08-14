
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
    invariant forall i :: 0 <= i < n ==> a[i] == (i-1)*(i-1)*(i-1) + 6*(i-1) + 1
  {
    a[n] := c;
    assert a[n] == n*n*n;
    c := c + k;
    k := k + m;
    m := m + 6;
    n := n + 1;
  }
}

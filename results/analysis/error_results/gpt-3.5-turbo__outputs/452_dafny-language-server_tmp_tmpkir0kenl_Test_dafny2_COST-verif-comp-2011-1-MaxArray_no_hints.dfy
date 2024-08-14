
method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{
  x := 0;
  var y := a.Length - 1;
  ghost var m := y;
  while x < y
    invariant 0 <= x <= y < a.Length
    invariant 0 <= m < a.Length
    invariant forall i :: 0 <= i < a.Length ==> a[i] <= a[m]
  {
    if a[x] <= a[y] {
      assert a[x] <= a[m];
      x := x + 1;  
      m := y;
    } else {
      assert a[y] <= a[m];
      y := y - 1;  
      m := x;
    }
  }
  assert forall i :: 0 <= i < a.Length ==> a[i] <= a[x];
  return x;
}

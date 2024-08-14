method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{
  x := 0;
  var y := a.Length - 1;
  ghost var m := x;
  while x != y
    invariant 0 <= x < a.Length
    invariant 0 <= y < a.Length
    invariant x <= y
    invariant forall i :: 0 <= i < a.Length && (i <= x || i >= y) ==> a[i] <= a[m]
  {
    if a[x] <= a[y] {
      x := x + 1;
      if x < a.Length {
        m := x;
      }
    } else {
      y := y - 1;
      if y >= 0 {
        m := y;
      }
    }
  }
  assert forall i :: 0 <= i < a.Length ==> a[i] <= a[m];
  return x;
}
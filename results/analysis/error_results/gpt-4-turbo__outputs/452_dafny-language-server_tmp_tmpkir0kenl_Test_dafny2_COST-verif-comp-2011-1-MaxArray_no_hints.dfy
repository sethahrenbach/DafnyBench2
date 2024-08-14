method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{
  x := 0;
  var y := a.Length - 1;
  ghost var m := x; // Initialize m to x

  while x != y
    invariant 0 <= x <= y < a.Length
    invariant forall i :: 0 <= i < x ==> a[i] <= a[x]
    invariant forall i :: y < i < a.Length ==> a[i] <= a[y]
    invariant a[x] <= a[m] && a[y] <= a[m]
    invariant m == x || m == y
  {
    if a[x] <= a[y] {
      x := x + 1;
      m := y;
    } else {
      y := y - 1;
      m := x;
    }
  }
  return x;
}
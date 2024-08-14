
method FindMax(a: array<int>) returns (i: int)
  requires a.Length > 0
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  var max := a[0];
  for k in 1..a.Length {
    if a[k] > max {
      max := a[k];
      i := k;
    }
  }
}

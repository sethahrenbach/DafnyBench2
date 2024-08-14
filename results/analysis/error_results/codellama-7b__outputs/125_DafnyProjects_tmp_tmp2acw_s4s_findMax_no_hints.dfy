
method findMax(a: array<real>) returns (max: real)
  requires a.Length > 0
  ensures exists k :: 0 <= k < a.Length && max == a[k]
  ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
{
  var max := a[0];
  for i := 1 to a.Length
  {
    if (a[i] > max) {
      max := a[i];
    }
  }
  return max;
}

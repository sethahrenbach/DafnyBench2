method FindMax(a: array<int>) returns (max: int)
   requires a != null && a.Length > 0;
   ensures 0 <= max < a.Length;
   ensures forall x :: 0 <= x < a.Length ==> a[max] >= a[x];
{
  var i := 0;
  max := 0;

  while (i < a.Length)
    invariant 0 <= i <= a.Length;
    invariant 0 <= max < a.Length;
    invariant forall j :: 0 <= j < i ==> a[max] >= a[j];
    invariant i > 0 ==> exists k :: 0 <= k < i && max == k;
  {
    if (a[i] > a[max]) { 
      max := i; 
    }
    i := i + 1;
  }
  assert 0 <= max < a.Length;
  assert forall j :: 0 <= j < a.Length ==> a[max] >= a[j];
  return max;
}
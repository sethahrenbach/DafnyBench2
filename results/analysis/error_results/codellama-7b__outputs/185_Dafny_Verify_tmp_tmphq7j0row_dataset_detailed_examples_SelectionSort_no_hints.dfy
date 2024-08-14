
method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n < a.Length
    invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i,j :: n <= i < j < a.Length ==> a[i] <= a[j]
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant 0 <= m < a.Length
      invariant forall i,j :: 0 <= i < j < m ==> a[i] <= a[j]
      invariant forall i,j :: m <= i < j < a.Length ==> a[i] <= a[j]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    if mindex != n {
      a[mindex], a[n] := a[n], a[mindex];
    }
    n := n + 1;
  }
}

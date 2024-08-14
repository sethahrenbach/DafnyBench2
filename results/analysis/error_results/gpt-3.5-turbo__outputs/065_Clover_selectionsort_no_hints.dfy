method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> a[k] <= a[n]
    invariant multiset(a[..n]) == old(multiset(a[..n]))
  {
    var mindex := n;
    var m := n + 1;
    while m < a.Length
      invariant n <= m <= a.Length
      invariant a[mindex] <= a[n]
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    assert forall k :: n <= k < a.Length ==> a[mindex] <= a[k];
    var temp := a[mindex];
    a[mindex] := a[n];
    a[n] := temp;
    n := n + 1;
  }
}
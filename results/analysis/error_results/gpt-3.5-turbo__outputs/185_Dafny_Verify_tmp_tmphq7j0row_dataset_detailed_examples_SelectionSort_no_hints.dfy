
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
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex := n;
    var m := n + 1;
    while m < a.Length
      invariant n <= m <= a.Length
      invariant n <= mindex < a.Length
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
      invariant multiset(a[..n]) == old(multiset(a[..n]))
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    if a[mindex] < a[n] {
      var temp := a[mindex];
      a[mindex] := a[n];
      a[n] := temp;
    }
    n := n + 1;
  }  
}

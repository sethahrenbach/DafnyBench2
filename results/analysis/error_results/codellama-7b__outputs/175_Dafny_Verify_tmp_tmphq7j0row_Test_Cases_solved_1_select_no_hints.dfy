
method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
  {
    var mindex, m := n, n;
    while m != a.Length
    {
      // Loop Invariant: a[0..n] is sorted
      assert forall k :: 0 <= k < n ==> a[k] <= a[n];

      // Loop Invariant: a[n+1..m] is sorted
      assert forall k :: n < k < m ==> a[k] <= a[m];

      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    // Postcondition: a[mindex] is the smallest element in a[n..m]
    assert a[mindex] <= a[n];

    if a[mindex] < a[n] {
      a[mindex], a[n] := a[n], a[mindex];
    }
    n := n + 1;
  }
}

predicate sorted (a: array<int>)
  requires a != null
  reads a
{
  sorted'(a, a.Length)
}

predicate sorted' (a: array<int>, i: int)
  requires a != null
  requires 0 <= i <= a.Length
  reads a
{
  forall k :: 0 < k < i ==> a[k-1] <= a[k]
}


// Selection sort on arrays

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
  ensures multiset(old(a[..])) == multiset(a[..])
{
  var n := 0;
  while (n != a.Length)
    invariant 0 <= n <= a.Length
    invariant sorted'(a, n)
    invariant multiset(old(a[..])) == multiset(a[..])
  {
    var mindex := n;
    var m := n + 1;
    while (m != a.Length)
      invariant n <= m <= a.Length
      invariant n <= mindex < a.Length
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
      invariant multiset(old(a[..])) == multiset(a[..])
    {
      if (a[m] < a[mindex]) {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
  assert sorted(a);
}
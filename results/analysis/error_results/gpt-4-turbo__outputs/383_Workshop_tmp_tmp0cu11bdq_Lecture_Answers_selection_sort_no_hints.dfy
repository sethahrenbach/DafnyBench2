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
{
  var n := 0;
  while (n < a.Length)
    invariant 0 <= n <= a.Length
    invariant sorted'(a, n)
    invariant forall k :: 0 <= k < n ==> a[k] <= a[k+1]
    invariant forall k :: n <= k < a.Length ==> exists j :: n <= j < a.Length && a[j] == old(a[k])
    decreases a.Length - n
  {
    var mindex := n;
    var m := n + 1;
    while (m < a.Length)
      invariant n <= m <= a.Length
      invariant n <= mindex < m
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
      invariant forall i :: n <= i < m ==> exists j :: n <= j < a.Length && a[j] == old(a[i])
      decreases a.Length - m
    {
      if (a[m] < a[mindex]) {
        mindex = m;
      }
      m = m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n = n + 1;
  }
}
predicate sorted(a: array<int>)
	requires a != null
	reads a
{
	sorted'(a, a.Length)
}

predicate sorted'(a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 <= k < i - 1 ==> a[k] <= a[k + 1]
}


// Selection sort on arrays

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
{
  var n := 0;
  while (n < a.Length)
    invariant 0 <= n <= a.Length
    invariant forall j :: 0 <= j < n ==> forall k :: n <= k < a.Length ==> a[j] <= a[k]
  {
    var mindex := n;
    var m := n + 1;
    while (m < a.Length)
      invariant n <= m <= a.Length
      invariant n <= mindex < a.Length
      invariant forall j :: n <= j < m ==> a[mindex] <= a[j]
    {
      if (a[m] < a[mindex]) {
        mindex := m;
      }
      m := m + 1;
    }
    assert forall k :: n <= k < a.Length ==> a[n] <= a[mindex];
    var temp := a[n];
    a[n] := a[mindex];
    a[mindex] := temp;
    n := n + 1;
  }
}
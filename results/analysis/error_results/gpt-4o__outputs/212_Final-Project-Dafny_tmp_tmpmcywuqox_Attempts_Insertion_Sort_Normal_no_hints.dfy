predicate sorted (a: array<int>)

	reads a
{
	sortedA(a, a.Length)
}

predicate sortedA (a: array<int>, i: int)

	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

method lookForMin (a: array<int>, i: int) returns (m: int)

	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
	var j := i;
	m := i;
	while(j < a.Length)
		// Invariant: i <= j <= a.Length
		// Invariant: i <= m < a.Length
		// Invariant: forall k :: i <= k < j ==> a[k] >= a[m]
		invariant i <= j <= a.Length
		invariant i <= m < a.Length
		invariant forall k :: i <= k < j ==> a[k] >= a[m]
	{
		if(a[j] < a[m]) { m := j; }
		j := j + 1;
	}
}

method insertionSort (a: array<int>)

	modifies a
	ensures sorted(a)
{
	var c := 0;
	while(c < a.Length)
		// Invariant: 0 <= c <= a.Length
		// Invariant: sortedA(a, c)
		invariant 0 <= c <= a.Length
		invariant sortedA(a, c)
		// Invariant: forall k :: 0 <= k < c ==> a[k] <= a[c]
		invariant forall k :: 0 <= k < c ==> a[k] <= a[c]
	{
		var m := lookForMin(a, c);
		a[m], a[c] := a[c], a[m];
		// Ensure that the array remains sorted up to c + 1
		assert forall k :: 0 < k < c ==> a[k-1] <= a[k];
		assert forall k :: 0 < k < c + 1 ==> a[k-1] <= a[k];
		c := c + 1;
	}
	// Ensure the entire array is sorted
	assert sortedA(a, a.Length);
}
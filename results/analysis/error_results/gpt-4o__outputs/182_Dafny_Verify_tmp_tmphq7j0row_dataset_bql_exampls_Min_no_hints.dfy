method min(a: array<int>, n : int) returns (min : int)
    requires 0 < n <= a.Length;
	ensures (exists i : int :: 0 <= i && i < n && a[i] == min);
	ensures (forall i : int :: 0 <= i && i < n ==> a[i] >= min);
{
	var i : int;

	min := a[0];
	i := 1;

	while (i < n)
		// Invariant: 0 <= i <= n
		// Invariant: (forall j : int :: 0 <= j < i ==> a[j] >= min)
		// Invariant: (exists j : int :: 0 <= j < i && a[j] == min)
	{
		if (a[i] < min) {
			min := a[i];
		}
		i := i + 1;
	}
	// Assert to help Dafny verify the postconditions
	assert (exists j : int :: 0 <= j < n && a[j] == min);
	assert (forall j : int :: 0 <= j < n ==> a[j] >= min);
}
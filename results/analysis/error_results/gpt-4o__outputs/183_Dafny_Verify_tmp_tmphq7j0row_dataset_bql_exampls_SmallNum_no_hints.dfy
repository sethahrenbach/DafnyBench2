method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
	requires n > 0;
    requires n <= a.Length;
	requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
	ensures r <= max * n;
{
	var i: int;	

	i := 0;
	r := 0;

	while (i < n)
		// Invariant: 0 <= i <= n
		// Invariant: r <= max * i
		// Invariant: (forall j: int :: 0 <= j < i ==> a[j] <= max)
		// Invariant: r == (sum k: int :: 0 <= k < i :: a[k])
	{
		assert 0 <= i < n;
		assert a[i] <= max;
		assert r + a[i] <= r + max;
		assert r + a[i] <= max * (i + 1); // Ensure the sum will not exceed max * (i + 1)
		r := r + a[i];
		assert r <= max * (i + 1); // Ensure the invariant holds after the addition
		i := i + 1;
	}
	assert r <= max * n;
}
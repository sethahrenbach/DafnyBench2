method square (n: int) returns (r: int)
	requires 0 <= n;
	ensures r == n*n;
{
	var x: int;
	var i: int;

	r := 0;
	i := 0;
	x := 1;

	while (i < n)
		invariant 0 <= i <= n &&
			r == i*x &&
			x == 2*i + 1 &&
			i <= n;
	{
		assert i < n;
		assert r + x == (i + 1) * x;
		assert x == 2 * i + 1;
		
		r := r + x;
		x := x + 2;
		i := i + 1;
	}
	assert r == n*n;
}

function fib(n: nat): nat
{
	if n == 0 then 0 else
	if n == 1 then 1 else
		fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
	requires n >= 0
	ensures b == fib(n)
{
	var i: int := 1;
	if 0 <= n < 2 { return n; }
	b := 1;
	var c := 1;
	
	while i < n
		invariant 1 <= i <= n
		invariant b == fib(i-1)
		invariant c == fib(i)
		invariant i <= n
	{
		b, c := c, b + c;
		i := i + 1;
	}
}

method Main()
{
	var ret := ComputeFib(5);
}

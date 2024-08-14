method mult(a:int, b:int) returns (x:int)
  	requires a >= 0 && b >= 0
  	ensures x == a * b
{
	x := 0;
	var i := 0;
	while i < a
		invariant x == b * i
		invariant 0 <= i <= a
	{
		x := x + b;
		i := i + 1;
	}
}
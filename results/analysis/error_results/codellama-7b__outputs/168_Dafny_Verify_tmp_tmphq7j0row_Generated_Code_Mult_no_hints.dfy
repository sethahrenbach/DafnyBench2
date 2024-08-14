
method mult(a:int, b:int) returns (x:int)
  	requires a >= 0 && b >= 0
  	ensures x == a * b
{
  	x := 0;
	var y := a;
  	loop invariant y >= 0; // y is always non-negative
  	loop invariant x == a * b - y * b; // x is equal to the product of a and b minus the product of y and b
  	loop assigns x, y; // x and y are the only variables modified in the loop
  	while y > 0
	{
		x := x + b;
		y := y - 1;
	}
}

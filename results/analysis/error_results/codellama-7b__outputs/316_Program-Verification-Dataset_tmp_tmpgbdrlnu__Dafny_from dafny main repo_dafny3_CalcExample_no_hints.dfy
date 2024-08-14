  method double(x: int) returns (y: int)
  ensures y == 2 * x
{
  y := x * 2;
}
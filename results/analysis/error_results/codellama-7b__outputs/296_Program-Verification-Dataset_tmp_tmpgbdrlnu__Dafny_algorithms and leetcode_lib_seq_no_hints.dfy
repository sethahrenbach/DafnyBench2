  method foo(x: int) returns (y: int)
  ensures y == x + 1
{
  y := x + 1;
}
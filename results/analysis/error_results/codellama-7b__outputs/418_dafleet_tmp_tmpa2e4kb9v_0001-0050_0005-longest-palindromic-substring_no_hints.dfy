
method foo(x: int) returns (y: int)
  ensures y == x
{
  if x < 0 then
    error "invalid input"
  else
    y := x
}

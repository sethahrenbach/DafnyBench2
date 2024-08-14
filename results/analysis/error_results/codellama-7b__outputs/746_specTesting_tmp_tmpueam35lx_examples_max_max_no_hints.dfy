
function foo(x: int, y: int): int
  requires x > 0 && y > 0
{
  if x > y then
    return x;
  else
    return y;
}

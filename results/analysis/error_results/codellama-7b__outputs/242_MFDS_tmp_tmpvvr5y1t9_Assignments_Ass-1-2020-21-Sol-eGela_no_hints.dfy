
function foo(x: int, y: int): int
  requires x >= 0 && y >= 0
  ensures result >= 0
{
  if x == 0 || y == 0 {
    return 0;
  }
  if x > y {
    return x;
  }
  if y > x {
    return y;
  }
  return x + y;
}

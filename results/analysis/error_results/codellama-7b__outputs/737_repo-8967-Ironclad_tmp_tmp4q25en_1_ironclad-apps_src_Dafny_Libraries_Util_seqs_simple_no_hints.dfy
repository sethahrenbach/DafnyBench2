
method foo(x: int): int
  requires x >= 0
  ensures x >= 0
{
  return x;
}

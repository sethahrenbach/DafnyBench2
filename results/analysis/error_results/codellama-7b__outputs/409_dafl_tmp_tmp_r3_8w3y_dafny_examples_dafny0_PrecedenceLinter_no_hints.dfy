  function f(x: int): int
  requires x >= 0
  ensures x >= 0
{
  if x < 10 then
    1
  else
    10
}
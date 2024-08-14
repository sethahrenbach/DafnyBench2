
function max(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures a >= b ==> result >= b
  ensures b >= a ==> result >= a
{
  if a > b then
    return a;
  else
    return b;
}

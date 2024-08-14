
method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
  loop invariant 0.0 <= r * r <= x
  loop assigns r
  loop variant x - r * r
{
  if x == 0.0 then
    return 0.0;
  else
    r := x / 2.0;
    while r * r > x do
      r := (r + x / r) / 2.0;
    return r;
}

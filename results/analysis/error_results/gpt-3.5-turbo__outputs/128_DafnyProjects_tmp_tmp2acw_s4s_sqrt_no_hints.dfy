
method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
{
  var r := 0.0;
  var guess := x;
  while (r * r != x)
    invariant 0.0 <= r <= guess;
    invariant r * r <= x;
    decreases |x - r * r|;
  {
    r := (r + x / r) / 2.0;
  }
  r
}

method testSqrt() {
  var r := sqrt(4.0);
  assert r * r == 4.0;
  assert r >= 0.0;
  if (r < 2.0) { monotonicSquare(r, 2.0); }
}

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
{
  assert c * x < c * y;
}

lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
{
  assert 0.0 < x * x < y * y;
  monotonicMult(x, x, y);
}

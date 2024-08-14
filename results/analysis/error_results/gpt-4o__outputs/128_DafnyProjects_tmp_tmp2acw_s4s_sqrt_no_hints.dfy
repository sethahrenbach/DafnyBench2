method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
{
  var low: real := 0.0;
  var high: real := if x < 1.0 then 1.0 else x;
  var mid: real;
  while high - low > 1e-10
    invariant low * low <= x
    invariant high * high >= x
    invariant low >= 0.0
    invariant high >= 0.0
  {
    mid := (low + high) / 2.0;
    if mid * mid < x {
      low := mid;
    } else {
      high := mid;
    }
  }
  r := (low + high) / 2.0;
}

method testSqrt() {
  var r := sqrt(4.0);
  //if (2.0 < r) { monotonicSquare(2.0, r); }
  if (r < 2.0) { monotonicSquare(r, 2.0); }
}

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
{}

lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
{
    monotonicMult(x, x, y);
    assert x * x < y * y;
}
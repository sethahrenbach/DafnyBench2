method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
{
  // Start with an initial guess of x/2
  r := x / 2.0;
  
  // Keep refining the guess until it's close enough
  while (r * r - x > 0.001 || x - r * r > 0.001)
  invariant r >= 0.0
  invariant r != 0.0 ==> x / (r * r) <= 4.0
  {
    r := (r + x / r) / 2.0;
  }
}

method testSqrt() {
  var r := sqrt(4.0);
  assert r * r == 4.0;
  //if (2.0 < r) { monotonicSquare(2.0, r); }
  if (r < 2.0) { 
    assert false; // Cannot happen, since sqrt(4.0) >= 2.0
  } else {
    assert 2.0 <= r; // Follows from the if condition
    monotonicSquare(2.0, r);
  }
}

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
{
  /* The assertion follows directly from the preconditions:
     x < y && c > 0.0
     ==> { arithmetic }
     c * x < c * y
  */
}


lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
{
  assert 0.0 < x; // Follows from precondition
  assert x < y; // Follows from precondition
  
  monotonicMult(x, x, y);
  monotonicMult(y, x, y);
}
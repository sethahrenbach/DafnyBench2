
method Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
{
  var m := x;
  var n := y;
  r := 0;

  while m > 0
  {
    // Loop invariant: r == x * y - m * n
    // This invariant is maintained throughout the loop
    assert r == x * y - m * n;

    r := r + n;
    m := m - 1;
  }

  // Postcondition: r == x * y
  assert r == x * y;

  return r;
}


method Mult(x:nat, y:nat) returns (r:nat)
  ensures r == x * y
{
  var m := x;
  var n := y;
  r := 0;
  while m > 0
  {
    // loop invariant: m*n + r = x*y
    assert m*n + r == x*y;
    r := r + n;
    m := m - 1;
  }
  // postcondition: r == x*y
  assert r == x*y;
  return r;
}

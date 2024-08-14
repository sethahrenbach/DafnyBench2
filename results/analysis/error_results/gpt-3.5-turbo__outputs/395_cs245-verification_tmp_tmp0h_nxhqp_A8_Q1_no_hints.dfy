
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n;

method A8Q1(y0: int, x: int) returns (z: int)
  requires y0 >= 0;
  ensures z == power(x, y0);
{
  var y := y0;  //This is here for Dafny's sake and immutable inputs...

  assert y == y0 && y >= 0; // Pre-Condition
  assert power(x, y0 - y) == 1 && y >= 0; // implied (a)

  z := 1;
  assert z == power(x, y0 - y) && y >= 0; // assignment

  while (y > 0)
    invariant z == power(x, y0 - y) && y >= 0;
    invariant y >= 0;
    invariant y <= y0;
  {
    assert z == power(x, y0 - y) && y >= 0 && y > 0; // partial-while
    assert z * x == power(x, y0 - (y - 1)) && y - 1 >= 0; // implied (b)

    z := z * x;
    assert z == power(x, y0 - (y - 1)) && y - 1 >= 0; // assignment

    y := y - 1;
    assert z == power(x, y0 - y) && y >= 0; // assignment
  }

  assert z == power(x, y0 - y) && y >= 0 && !(y > 0); // partial-while
  assert z == power(x, y0); // implied (c)
}

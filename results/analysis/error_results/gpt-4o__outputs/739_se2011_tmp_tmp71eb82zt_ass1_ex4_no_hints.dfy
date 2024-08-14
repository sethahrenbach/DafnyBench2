method Eval(x:int) returns (r:int)
requires x >= 0
ensures r == x*x
{
  var y:int := x;
  var z:int := 0;
  // Loop invariant
  invariant y >= 0;
  invariant z == x * (x - y);
  while y > 0
  {
    invariant y >= 0;
    invariant z == x * (x - y);
    z := z + x;
    y := y - 1;
  }
  assert y == 0;
  assert z == x * x;
  r := z;
}
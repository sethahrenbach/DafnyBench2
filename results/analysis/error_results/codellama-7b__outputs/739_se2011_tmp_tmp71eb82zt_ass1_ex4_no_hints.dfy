
method Eval(x:int) returns (r:int)
  requires x >= 0
  ensures r == x*x
{
  var y:int := x;
  var z:int := 0;
  loop invariant y >= 0;
  loop invariant z == x*y;
  while y > 0
  {
    z := z + x;
    y := y - 1;
  }
  return z;
}

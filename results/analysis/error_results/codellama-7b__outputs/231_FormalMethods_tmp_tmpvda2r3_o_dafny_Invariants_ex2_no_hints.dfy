
function Potencia(x:bitvector, y:bitvector):bitvector
{
  if y == 0
  then 1
  else x * Potencia(x, y-1)
}

method Pot(x:bitvector, y:bitvector) returns (r:bitvector)
ensures r == Potencia(x,y)
{
  r := 1;
  var b := x;
  var e := y;
  while e > 0
  {
    // Loop Invariant: r == b^e
    assert r == b^e;
    r := r * b;
    e := e - 1;
  }

  return r;
}

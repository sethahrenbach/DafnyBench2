method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{
  var i:int := 0;
  r := x;
  while (i < y)
    invariant 0 <= i <= y && r == x + i;
    decreases y - i;
  {
    r := r + 1;
    i := i + 1;
  }
  return r;
}
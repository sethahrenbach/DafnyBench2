
function power(a: int, n: int): int
  requires 0 <= n;

method A8Q1(y0: int, x: int) returns (z: int)
  requires y0 >= 0;
  ensures z == power(x, y0);
{
  var y := y0;

  loopInvariant y >= 0;
  loopInvariant z == power(x, y0 - y);
  loopAssume y > 0;

  while (y > 0)
  {
    loopInvariant z == power(x, y0 - y);
    loopAssume y > 0;

    z := z * x;
    y := y - 1;
  }

  loopInvariant z == power(x, y0 - y);
  loopAssume y <= 0;
}

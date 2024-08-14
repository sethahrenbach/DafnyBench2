method M1(x: int, y: int) returns (r: int)
  ensures r == x * y
{
  if (x == 0) {
    r := 0;
  } else if (x < 0) {
    r := M1(-x, y);
    r := -r;
  } else {
    r := 0;
    var i := x;
    while (i > 0)
      decreases i
      invariant r + i * y == x * y
    {
      r := r + y;
      i := i - 1;
    }
  }
}

method A1(x: int, y: int) returns (r: int)
  ensures r == x + y
{
  r := x;
  if (y < 0) {
    var n := y;
    while (n != 0)
      invariant r + n == x + y
      invariant n <= 0
      decreases -n
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while (n != 0)
      invariant r - n == x
      invariant n >= 0
      decreases n
    {
      r := r + 1;
      n := n - 1;
    }
  }
}
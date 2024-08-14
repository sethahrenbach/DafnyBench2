
method mySqrt(x: int) returns (res: int)
  requires 0 <= x;
  ensures sqrt(x, res);
{
  var l, r := 0, x;
  loop invariant 0 <= l <= r;
  loop invariant sqrt(x, l) && sqrt(x, r) ==> l == r;
  loop invariant sqrt(x, l) && sqrt(x, r) ==> l*l <= x && (l+1)*(l+1) > x;
  loop invariant sqrt(x, l) && sqrt(x, r) ==> r*r <= x && (r+1)*(r+1) > x;
  while (l <= r)
  {
    var mid := (l + r) / 2;
    if (mid * mid <= x && (mid + 1) * (mid + 1) > x) {
      return mid;
    } else if (mid * mid <= x) {
      l := mid + 1;
    } else {
      r := mid - 1;
    }
  }
}

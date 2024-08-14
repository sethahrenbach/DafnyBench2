
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
  k, m := 0, 0;
  var s := 0;  // invariant s == Sum(a, k, m)
  var n := 0;
  var c, t := 0, 0;  // invariant t == Sum(a, c, n)
  while n < |a}
    invariant 0 <= n <= |a|
    invariant 0 <= c <= n
    invariant t == Sum(a, c, n)
    invariant 0 <= k <= m <= |a|
    invariant forall p, q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
    invariant s == Sum(a, k, m)
  {
    t, n := t + a[n], n + 1;
    if t < 0 {
      c, t := n, 0;
    } else if s < t {
      k, m, s := c, n, t;
    }
  }
}

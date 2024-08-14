// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
  ensures Sum(a, s, t) == if s == t then 0 else Sum(a, s, t-1) + a[t-1]
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
  k, m := 0, 0;
  var s := 0;
  var n := 0;
  var c, t := 0, 0;
  while n < |a|
    invariant 0 <= n <= |a|
    invariant 0 <= c <= n <= |a|
    invariant s == Sum(a, k, m)
    invariant t == Sum(a, c, n)
    invariant forall p,q :: 0 <= p <= q <= n ==> Sum(a, p, q) <= s
  {
    assert 0 <= n < |a|; // Ensure n is within bounds before accessing a[n]
    t, n := t + a[n], n + 1;
    if t < 0 {
      c, t := n, 0;
    } else if s < t {
      k, m, s := c, n, t;
    }
    assert 0 <= c <= n <= |a|;
    assert s == Sum(a, k, m);
    assert t == Sum(a, c, n);
    assert forall p,q :: 0 <= p <= q <= n ==> Sum(a, p, q) <= s;
  }
  assert 0 <= k <= m <= |a|;
  assert forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m);
}
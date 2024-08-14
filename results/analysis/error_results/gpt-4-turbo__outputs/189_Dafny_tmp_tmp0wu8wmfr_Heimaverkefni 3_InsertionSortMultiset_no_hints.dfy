
method Search(s: seq<int>, x: int) returns (k: int)
  requires forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures 0 <= k <= |s|
  ensures forall i | 0 <= i < k :: s[i] <= x
  ensures forall i | k <= i < |s| :: x <= s[i]
{
  var low := 0;
  var high := |s|;
  while low < high
    invariant 0 <= low <= high <= |s|
    invariant forall i | 0 <= i < low :: s[i] <= x
    invariant forall i | high <= i < |s| :: x <= s[i]
    decreases high - low
  {
    var mid := (low + high) / 2;
    if s[mid] > x {
      high := mid;
    } else {
      low := mid + 1;
    }
  }
  return low;
}

method Sort(m: multiset<int>) returns (r: seq<int>)
  ensures multiset(r) == m
  ensures forall p, q | 0 <= p < q < |r| :: r[p] <= r[q]
{
  r := [];
  var rest := m;
  while rest != multiset{}
    invariant multiset(r) + rest == m
    invariant forall p, q | 0 <= p < q < |r| :: r[p] <= r[q]
    decreases rest
  {
    var x :| x in rest;
    rest := rest - multiset{x};
    var k := Search(r, x);
    r := r[..k] + [x] + r[k..];
  }
}

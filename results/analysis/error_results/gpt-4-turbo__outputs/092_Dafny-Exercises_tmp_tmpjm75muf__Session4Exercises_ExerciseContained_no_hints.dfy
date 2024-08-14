predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
  requires n <= m && n >= 0
  requires strictSorted(v[..n])
  requires strictSorted(w[..m])
  requires v.Length >= n && w.Length >= m
  ensures b == forall k :: 0 <= k < n ==> v[k] in w[..m]
{
  var i := 0;
  var j := 0;
  while (i < n && j < m)
    invariant 0 <= i <= n
    invariant 0 <= j <= m
    invariant forall k :: 0 <= k < i ==> exists l :: 0 <= l < m && v[k] == w[l]
    decreases n - i, m - j
  {
    if (v[i] == w[j]) {
      i := i + 1;
    }
    if (v[i] > w[j]) {
      j := j + 1;
    } else {
      // v[i] is less than w[j] and not found in w[..j], so it cannot be in w[..m]
      break;
    }
  }
  b := i == n;
}
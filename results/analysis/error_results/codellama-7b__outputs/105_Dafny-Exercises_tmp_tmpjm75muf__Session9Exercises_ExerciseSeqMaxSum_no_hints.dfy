
function segSumaMaxima2(v: array<int>, i: int) returns (s: int, k: int)
  requires v.Length > 0 && 0 <= i < v.Length
  ensures 0 <= k <= i && s == Sum2(v, k, i + 1) && SumMaxToRight2(v, i, s)
{
  s := v[i];
  k := i;
  var j := i;
  var maxs := s;
  while (j > 0) {
    s := s + v[j - 1];
    if (s > maxs) {
      maxs := s;
      k := j - 1;
    }
    j := j - 1;
  }
  s := maxs;
}

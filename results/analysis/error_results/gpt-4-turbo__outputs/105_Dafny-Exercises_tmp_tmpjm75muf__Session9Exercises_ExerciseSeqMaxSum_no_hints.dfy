
function Sum(v: array<int>, i: int, j: int): int
  reads v
  requires 0 <= i <= j <= v.Length
{
  if (i == j) then 0
  else Sum(v, i, j-1) + v[j-1]
}

predicate SumMaxToRight(v: array<int>, i: int, s: int)
  reads v
  requires 0 <= i < v.Length
{
  forall l, ss :: 0 <= l <= i && ss == i+1 ==> Sum(v, l, ss) <= s
}

method segMaxSum(v: array<int>, i: int) returns (s: int, k: int)
  requires v.Length > 0 && 0 <= i < v.Length
  ensures 0 <= k <= i && s == Sum(v, k, i+1) && SumMaxToRight(v, i, s)
{
  s := v[i];
  k := i;
  var maxs := s;
  for j := i-1 downto 0
    invariant 0 <= j < i
    invariant i >= k >= j
    invariant maxs == Sum(v, k, i+1)
    invariant forall l, ss :: j < l <= i && ss == i+1 ==> Sum(v, l, ss) <= maxs
    decreases j
  {
    var currentSum := Sum(v, j, i+1);
    if (currentSum > maxs) {
      maxs := currentSum;
      k := j;
    }
  }
  s := maxs;
}

function Sum2(v: array<int>, i: int, j: int): int
  reads v
  requires 0 <= i <= j <= v.Length
{
  if (i == j) then 0
  else v[i] + Sum2(v, i+1, j)
}

predicate SumMaxToRight2(v: array<int>, j: int, i: int, s: int)
  reads v
  requires 0 <= j <= i < v.Length
{
  forall l, ss :: j <= l <= i && ss == i+1 ==> Sum2(v, l, ss) <= s
}

method segSumaMaxima2(v: array<int>, i: int) returns (s: int, k: int)
  requires v.Length > 0 && 0 <= i < v.Length
  ensures 0 <= k <= i && s == Sum2(v, k, i+1) && SumMaxToRight2(v, 0, i, s)
{
  s := v[i];
  k := i;
  var maxs := s;
  for j := i-1 downto 0
    invariant 0 <= j <= i
    invariant i >= k >= j
    invariant maxs >= s
    invariant forall l, ss :: j <= l <= i && ss == i+1 ==> Sum2(v, l, ss) <= maxs
    decreases j
  {
    var newSum := s + v[j];
    if (newSum > maxs) {
      maxs = newSum;
      k = j;
    }
    s = newSum;
  }
  s = maxs;
}

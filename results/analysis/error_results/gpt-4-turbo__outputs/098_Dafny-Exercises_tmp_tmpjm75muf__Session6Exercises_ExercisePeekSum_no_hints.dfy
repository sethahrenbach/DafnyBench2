predicate isPeek(v: array<int>, i: int)
  reads v
  requires 0 <= i < v.Length
  { forall k :: 0 <= k < i ==> v[i] >= v[k] }

function peekSum(v: array<int>, i: int): int
  reads v
  requires 0 <= i <= v.Length
{
  if (i == 0) then 0
  else if isPeek(v, i-1) then v[i-1] + peekSum(v, i-1)
  else peekSum(v, i-1)
}

method mPeekSum(v: array<int>) returns (sum: int)
  requires v.Length > 0
  ensures sum == peekSum(v, v.Length)
{
  var i := 1;
  sum := v[0];
  var lmax := v[0];
  while (i < v.Length)
    invariant 1 <= i <= v.Length
    invariant sum == peekSum(v, i)
    invariant lmax == v[i-1]
    invariant forall k :: 0 <= k < i ==> (isPeek(v, k) ==> v[k] <= lmax)
    invariant forall k :: 0 <= k < i && isPeek(v, k) ==> sum >= peekSum(v, k+1) + (if isPeek(v, k) then v[k] else 0)
  {
    if (v[i] >= lmax) {
      sum := sum + v[i];
      lmax := v[i];
    }
    i := i + 1;
  }
}
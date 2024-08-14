
function Sum(v:array<int>,i:int,j:int):int
  reads v
  requires 0<=i<=j<=v.Length
{
  if (i==j) then 0
  else Sum(v,i,j-1)+v[j-1]
}

predicate SumMaxToRight(v:array<int>,i:int,s:int)
  reads v
  requires 0<=i<v.Length
{
  forall l,ss {:induction l}::0<=l<=i && ss==i+1==> Sum(v,l,ss)<=s
}

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
  requires v.Length>0 && 0<=i<v.Length
  ensures 0<=k<=i && s==Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
{
  var j := 0;
  var s0 := v[0];
  var k0 := 0;
  while j < i
    invariant 0<=j<=i
    invariant s == Sum(v,k,j) && k<=j
    invariant SumMaxToRight(v,j,s)
  {
    if s + v[j] > v[j] {
      s := s + v[j];
    } else {
      k := j;
      s := v[j];
    }
    j := j+1;
  }
}

function Sum2(v:array<int>,i:int,j:int):int
  reads v
  requires 0<=i<=j<=v.Length
{
  if (i==j) then 0
  else v[i]+Sum2(v,i+1,j)
}

predicate SumMaxToRight2(v:array<int>,j:int,i:int,s:int)
  reads v
  requires 0<=j<=i<v.Length
{
  (forall l,ss {:induction l}::j<=l<=i && ss==i+1 ==> Sum2(v,l,ss)<=s)
}

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
  requires v.Length>0 && 0<=i<v.Length
  ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
{
  var j := i;
  var s0 := v[i];
  var k0 := i;
  var maxs := s0;
  while j > 0
    invariant 0<=j<=i+1
    invariant s == Sum2(v,k,i+1) && k<=i && SumMaxToRight2(v,j,i,s)
    invariant maxs == Sum2(v,k0,i+1) && k0<=i && SumMaxToRight2(v,0,i,maxs)
    decreases j
  {
    s := s + v[j-1];
    if s > maxs {
      maxs := s;
      k0 := j-1;
    }
    j := j-1;
  }
  s := maxs;
}

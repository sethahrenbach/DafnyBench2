//power -- Stephanie Renee McIntyre
//Based on the code used in the course overheads for Fall 2018

function power(a: int, n: int): int 
  requires 0 <= a && 0 <= n;

method compute_power(a: int, n: int) returns (s: int)
  requires n >= 0 && a >= 0;
  ensures s == power(a,n);
{
  assert 1 == power(a,0) && 0<=n;
  s := 1;
  var i := 0;
  assert s == power(a,i) && i<=n;
  while (i < n)
    invariant s == power(a,i) && i<=n;
    invariant 0 <= i <= n;
    invariant i <= n;
  {
    assert s == power(a,i) && i<=n && i<n;
    assert s*a == power(a,i+1) && i+1<=n;
    s := s*a;
    i := i+1;
  }
  assert s == power(a,n);
}
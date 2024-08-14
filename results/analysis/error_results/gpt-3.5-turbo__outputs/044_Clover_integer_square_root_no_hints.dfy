
method SquareRoot(N:nat) returns (r:nat)
  requires N >= 0
  ensures r*r <= N < (r+1)*(r+1)
{
  r:=0;
  while (r+1)*(r+1)<=N
    invariant r*r <= N && N < (r+1)*(r+1)
  {
    r:=r+1;
  }
  assert r*r <= N < (r+1)*(r+1);
}

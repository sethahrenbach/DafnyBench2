  I apologize for the mistake. Here is the corrected code:

method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
  loop invariant 0 <= r <= N
  loop invariant (r+1)*(r+1) <= N
{
  r:=0;
  while (r+1)*(r+1)<=N
  {
    r:=r+1;
  }
  return r;
}
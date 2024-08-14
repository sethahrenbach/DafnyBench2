
method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  loop
    invariant r >= 0;
    invariant q >= 0;
    invariant r + y * q == x;
    assigns r, q;

    r:=x;
    q:=0;
    while y<=r
    {
      assert y <= r;
      r:=r-y;
      q:=q+1;
    }
}

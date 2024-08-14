
method Max (x: nat, y:nat) returns (r:nat)
    ensures (r >= x && r >=y)
    ensures (r == x || r == y)
    loop invariant r >= x
    loop invariant r >= y
    loop assigns r
{
    if (x >= y) { r := x;}
    else { r := y;}
}

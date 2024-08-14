function max(x:nat, y:nat) : nat
{
  if (x < y) then y else x
}

method slow_max(a: nat, b: nat) returns (z: nat)
  requires true
  ensures z == max(a, b)
{
  z := 0;
  var x := a;
  var y := b;
  while (z < a && z < b)
    invariant z <= a
    invariant z <= b
    invariant z >= 0
    invariant x >= 0
    invariant y >= 0
    invariant x + y == a + b
    {
    z := z + 1;
    x := x - 1;
    y := y - 1;
    }

  assert z <= a && z <= b;

  if (x <= y) { return b; }
  else { return a; }
}
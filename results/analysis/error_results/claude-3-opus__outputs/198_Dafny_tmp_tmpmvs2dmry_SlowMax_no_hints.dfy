function max(x:nat, y:nat) : nat
{
  if (x < y) then y else x
}

method slow_max(a: nat, b: nat) returns (z: nat)
  ensures z == max(a, b)
{
  z := 0;
  var x := a;
  var y := b;
  while (x > z && y > z)
    invariant z <= x && z <= y
    invariant x <= a && y <= b
    invariant z <= max(x, y) == max(a, b)
    decreases max(x, y) - z
  {
    z := z + 1;
    x := x - 1;
    y := y - 1;
  }
  // At this point, either x == z or y == z (or both)
  assert x == z || y == z;
  // If x == z, then y >= z, so max(a, b) == max(x, y) == y
  // If y == z, then x >= z, so max(a, b) == max(x, y) == x
  if (x == z) {
    assert y >= z;
    assert max(a, b) == y;
    return y;
  } else {
    assert x >= z;
    assert max(a, b) == x;
    return x;
  }
}

method Fact(x: int) returns (y: int)
  requires x >= 0;
{
  y := 1;
  var z := 0;
  while(z != x)
  {
    // Loop Invariant: y = 1 * (1 + ... + z)
    assert y == 1 * (1 + ... + z);

    // Loop Invariant: z <= x
    assert z <= x;

    z := z + 1;
    y := y * z;
  }

  // Postcondition: y = 1 * (1 + ... + x)
  assert y == 1 * (1 + ... + x);
}

method Main() {
  var a := Fact(87);
  print a;
}

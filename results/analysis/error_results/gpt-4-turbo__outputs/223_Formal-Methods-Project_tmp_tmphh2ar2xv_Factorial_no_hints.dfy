method Fact(x: int) returns (y: int)
  requires x >= 0   
{
    y := 1;
    var z := 0;
    while z != x
      invariant 0 <= z <= x
      invariant y == if z == 0 then 1 else product(1, z)
    {
        z := z + 1;
        y := y * z;
    }
}

function product(a: int, b: int): int
  requires a >= 1 && b >= a
{
    if a > b then 1 else a * product(a + 1, b)
}

method Main() {
    var a := Fact(87);
    print a;
}
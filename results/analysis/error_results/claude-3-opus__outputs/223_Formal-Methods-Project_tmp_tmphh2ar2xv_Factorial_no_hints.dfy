method Fact(x: int) returns (y: int)
  requires x >= 0;
{
    y := 1;
    var z := 1;
    while(z <= x)
      invariant 1 <= z <= x + 1;
      invariant y == Factorial(z - 1);
    {
        y := y * z;
        z := z + 1;
    }
}

function Factorial(x: int): int
{
    if x <= 0 then 1 else x * Factorial(x-1)
}

method Main() {
    var a := Fact(87);
    print a;
}
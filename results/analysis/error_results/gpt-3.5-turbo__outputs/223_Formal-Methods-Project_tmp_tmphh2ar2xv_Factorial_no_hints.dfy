
method Fact(x: int) returns (y: int)
  requires x >= 0;   
  ensures y == Factorial(x);
{
    y := 1;
    var z := 0;
    while z < x
      invariant z <= x
      invariant y == Factorial(z)
      decreases x - z;
    {
        z := z + 1;
        y := y * z;
    }
}

function Factorial(n: int): int
{
    if n == 0 then 1
    else n * Factorial(n - 1)
}

method Main() {
    var a := Fact(87);
    print a;
}

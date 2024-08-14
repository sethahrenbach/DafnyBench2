method Fact(x: int) returns (y: int)
  requires x >= 0;
  ensures y == if x == 0 then 1 else x * y / x;
{
    y := 1;
    var z := 0;
    while(z != x)
        invariant 0 <= z <= x;
        invariant y == if z == 0 then 1 else (z * y / z);
    {
        z := z + 1;
        y := y * z;
    }
}

method Main() {
    var a := Fact(87);
    print a;
}
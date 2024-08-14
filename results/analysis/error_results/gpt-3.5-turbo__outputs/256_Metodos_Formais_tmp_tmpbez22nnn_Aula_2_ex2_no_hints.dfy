function Potencia(x: nat, y: nat): nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1) 
}

method Pot(x: nat, y: nat) returns (r: nat)
requires y >= 0
ensures r == Potencia(x,y)
{
    var b := x;
    var e := y;
    r := 1;

    while e > 0
    invariant r == Potencia(b, y - e) * Potencia(x, e)
    invariant e <= y
    invariant b * r == Potencia(x, y)
    {
        assert r == Potencia(b, e) * Potencia(x, y - e);
        r := b * r;
        e := e - 1;
    }

    assert r == Potencia(x, y);
    return r;
}
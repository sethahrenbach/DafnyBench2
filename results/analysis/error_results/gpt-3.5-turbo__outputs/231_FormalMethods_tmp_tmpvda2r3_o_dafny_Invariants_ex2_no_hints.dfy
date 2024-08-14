
function Potencia(x:nat, y:nat):nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1)
}

method Pot(x:nat, y:nat) returns (r:nat)
requires y >= 0
ensures r == Potencia(x,y)
{
    r := 1;
    var b := x;
    var e := y;
    while e > 0
    invariant r == Potencia(b, e) * r == Potencia(x, y)
    decreases e
    {
        assert r == Potencia(b, e) * r == Potencia(x, y);
        r := r * b;
        e := e - 1;
    }
    assert r == Potencia(b, e) * r == Potencia(x, y);

    return r;
}

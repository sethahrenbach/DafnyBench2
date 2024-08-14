
method div_ent_it(a: int, b: int) returns (c: int, r: int)
{
    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
    loop invariant c >= 0 && r >= 0
    loop invariant c*b + r == a
    loop assigns c, r
{
    c := 0; r := a ;
    while (r >= b)
    {
        c := c + 1 ;
        r := r - b ;
    }
}

method Main()
{
    var c, r := div_ent_it(6 , 2) ;
    print "Cociente: ", c, ", Resto: ", r ;
}

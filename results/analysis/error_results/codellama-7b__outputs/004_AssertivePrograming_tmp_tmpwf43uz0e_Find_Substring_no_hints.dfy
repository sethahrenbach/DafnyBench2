
method foo(x: int)
    requires x > 0
    ensures x > 0
{
    if x == 0 then
        assert false;
    else
        assert x > 0;
}

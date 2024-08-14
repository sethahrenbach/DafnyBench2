
method abs(x: int): int
    requires x >= 0
    ensures x >= 0
{
    if x >= 0 then
        return x;
    else
        return -x;
}

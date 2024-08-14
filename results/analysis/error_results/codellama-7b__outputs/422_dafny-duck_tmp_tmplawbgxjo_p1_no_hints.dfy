
function Sum(xs: seq<int>): int
    ensures Sum(xs[..]) == Sum(xs[..i]) + xs[i]
{
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
    loop invariant 0 <= i <= xs.Length
    loop invariant s == Sum(xs[..i])
{
    s := 0;
    var i := 0;
    while i < xs.Length
    {
        s := s + xs[i];
        i := i + 1;
    }
}


function Sum(xs: seq<int>): int
    ensures result == Sum(xs)
{
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
{
    s := 0;
    var i := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant s == Sum(xs[..i])
    {
        s := s + xs[i];
        i := i + 1;
    }
}

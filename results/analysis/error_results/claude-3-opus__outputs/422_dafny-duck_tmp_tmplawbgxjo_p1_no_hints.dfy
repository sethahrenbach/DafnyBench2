// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
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
        // The following assert statement helps prove the loop invariant
        assert forall j :: 0 <= j < i ==> s == Sum(xs[..j]);
        assert Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i];
        s := s + xs[i];
        i := i + 1;
    }
}

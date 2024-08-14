method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];

    // Loop invariant
    // 1. 0 <= i <= a.Length
    // 2. minVal == Min(a[..i])
    // 3. maxVal == Max(a[..i])
    for i := 1 to a.Length
        invariant 0 <= i <= a.Length
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
    {
        assert 0 <= i < a.Length;
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
        assert minVal == Min(a[..i+1]);
        assert maxVal == Max(a[..i+1]);
    }
    sum := minVal + maxVal;
}

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
    ensures forall i :: 0 <= i < |a| ==> a[i] >= Min(a)
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}

function Max(a: seq<int>) : int
    requires |a| > 0
    ensures forall i :: 0 <= i < |a| ==> a[i] <= Max(a)
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}
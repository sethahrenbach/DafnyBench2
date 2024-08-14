
method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];

    for i := 1 to a.Length
    {
        assert a[i] <= minVal || a[i] >= maxVal;
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    diff := maxVal - minVal;
}

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
{
    // Loop invariant: minPrefix is the minimum value in the prefix of a that has been processed so far.
    var minPrefix := Min(a[..|a|-1]);
    // Assertion: a[|a|-1] is either the minimum or maximum value in the prefix of a that has
    // been processed so far.
    assert a[|a|-1] <= minPrefix;
    if |a| == 1 then a[0]
    else
        if a[|a|-1] <= minPrefix then a[|a|-1] else Min(a[..|a|-1])
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    // Loop invariant: maxPrefix is the maximum value in the prefix of a that has been processed so far.
    var maxPrefix := Max(a[..|a|-1]);
    // Assertion: a[|a|-1] is either the minimum or maximum value in the prefix of a that has
    // been processed so far.
    assert a[|a|-1] >= maxPrefix;
    if |a| == 1 then a[0]
    else
        if a[|a|-1] >= maxPrefix then a[|a|-1] else Max(a[..|a|-1])
}


method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{
    var minVal := a[0];
    var maxVal := a[0];
    for i := 1 to a.Length
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    diff := maxVal - minVal;
}

function Min(a: seq<int>) : (m: int)
    requires |a| > 0
{
    var minPrefix := Min(a[..|a|-1]);
    if a[|a|-1] <= minPrefix {
        minPrefix := a[|a|-1];
    }
    return minPrefix;
}

function Max(a: seq<int>) : (m: int)
    requires |a| > 0
{
    var maxPrefix := Max(a[..|a|-1]);
    if a[|a|-1] >= maxPrefix {
        maxPrefix := a[|a|-1];
    }
    return maxPrefix;
}

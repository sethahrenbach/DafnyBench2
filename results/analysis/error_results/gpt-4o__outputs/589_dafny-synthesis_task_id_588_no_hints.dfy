method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];

    // Loop invariant
    // - minVal is the minimum value in the subarray a[0..i)
    // - maxVal is the maximum value in the subarray a[0..i)
    // - 0 <= i <= a.Length
    for i := 1 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> minVal <= a[j]
        invariant forall j :: 0 <= j < i ==> maxVal >= a[j]
        invariant exists j :: 0 <= j < i && minVal == a[j]
        invariant exists j :: 0 <= j < i && maxVal == a[j]
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    diff := maxVal - minVal;
    assert minVal == Min(a[..a.Length]);
    assert maxVal == Max(a[..a.Length]);
    assert diff == Max(a[..a.Length]) - Min(a[..a.Length]);
}

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
    ensures forall i :: 0 <= i < |a| ==> a[i] >= Min(a)
    ensures exists i :: 0 <= i < |a| && Min(a) == a[i]
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}

function Max(a: seq<int>) : int
    requires |a| > 0
    ensures forall i :: 0 <= i < |a| ==> a[i] <= Max(a)
    ensures exists i :: 0 <= i < |a| && Max(a) == a[i]
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}
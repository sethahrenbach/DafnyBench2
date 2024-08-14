method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];

    for i := 0 to a.Length - 1
        invariant 0 <= i < a.Length
        invariant forall j :: 0 <= j <= i ==> a[j] <= maxVal
        invariant forall j :: 0 <= j <= i ==> a[j] >= minVal
        invariant minVal == Min(a[0..i+1])
        invariant maxVal == Max(a[0..i+1])
    {
        if a[i] < minVal {
            minVal := a[i];
        }
        if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    sum := minVal + maxVal;
}

function Min(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        min Min(a[|a|-1], minPrefix)
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        max Max(a[|a|-1], maxPrefix)
}
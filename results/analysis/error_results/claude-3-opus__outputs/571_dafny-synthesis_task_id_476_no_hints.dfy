method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];

    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
    {
        if a[i] < minVal {
            minVal := a[i];
        }
        else if a[i] > maxVal {
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
        var m := Min(a[..|a|-1]);
        if a[|a|-1] < m then a[|a|-1] else m
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var m := Max(a[..|a|-1]);
        if a[|a|-1] > m then a[|a|-1] else m
}
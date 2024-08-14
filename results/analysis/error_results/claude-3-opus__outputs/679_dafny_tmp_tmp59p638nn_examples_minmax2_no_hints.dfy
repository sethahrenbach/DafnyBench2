method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{
    var minVal := a[0];
    var maxVal := a[0];
    
    // Loop invariant: 
    // - minVal is less than or equal to all values in a[0..i]
    // - maxVal is greater than or equal to all values in a[0..i]
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> minVal <= a[j]
      invariant forall j :: 0 <= j < i ==> maxVal >= a[j]
    {
        if a[i] < minVal {
            minVal := a[i];
        }
        if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    
    // After the loop, minVal and maxVal hold the minimum and maximum values of the entire array
    // We need to prove that minVal == Min(a[..]) and maxVal == Max(a[..])
    
    // Prove minVal == Min(a[..])
    assert forall i :: 0 <= i < a.Length ==> minVal <= a[i];
    assert minVal in a[..];
    
    // Prove maxVal == Max(a[..])
    assert forall i :: 0 <= i < a.Length ==> maxVal >= a[i];
    assert maxVal in a[..];
    
    diff := maxVal - minVal;
}

function Min(a: seq<int>) : (m: int)
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
      var minPrefix := Min(a[..|a|-1]);
      if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}

function Max(a: seq<int>) : (m: int)
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
      var maxPrefix := Max(a[..|a|-1]);
      if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}
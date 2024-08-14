
method CubeElements(a: array<int>) returns (cubed: array<int>)
    requires a != null
    requires a.Length > 0
    ensures cubed != null
    ensures cubed.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
{
    var cubedArray := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> cubedArray[j] == a[j] * a[j] * a[j]
    {
        cubedArray[i] := a[i] * a[i] * a[i];
        i := i + 1;
    }
    return cubedArray;
}

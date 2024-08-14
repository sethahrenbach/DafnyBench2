method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result <==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result <==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
{
    result := false;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant !result ==> forall k :: 0 <= k < i ==> forall j :: 0 <= j < b.Length ==> a[k] != b[j]
    {
        var j := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant !result ==> forall k :: 0 <= k < i ==> a[k] != b[j]
        {
            if a[i] == b[j] {
                result := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
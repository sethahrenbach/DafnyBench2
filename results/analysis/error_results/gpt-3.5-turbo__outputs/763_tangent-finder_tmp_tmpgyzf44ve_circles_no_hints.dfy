
method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j] // values in x will be in ascending order or empty
    requires forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) ==> (r[i] >= 0 && x[j] >= 0)       // x and r will contain no negative values
    ensures !b ==> forall i, j :: 0 <= i< r.Length && 0 <= j < x.Length ==> r[i] != x[j]   
    ensures b ==> exists i, j :: 0 <= i< r.Length && 0 <= j < x.Length && r[i] == x[j]
{
    var tempB := false;
    var k := 0;
    while k < r.Length && !tempB
        invariant 0 <= k <= r.Length
        invariant tempB <==> exists i, j :: 0 <= i < k && 0 <= j < x.Length :: r[i] == x[j]
        invariant !tempB ==> forall i, j :: 0 <= i < k && 0 <= j < x.Length :: r[i] != x[j]
    {
        var l := 0;
        var tangentMissing := false;
        while l < x.Length && !tangentMissing
            invariant 0 <= l <= x.Length
            invariant !tangentMissing ==> forall j :: 0 <= j < l :: r[k] != x[j]
            invariant tangentMissing ==> exists j :: 0 <= j < l :: r[k] != x[j]
        {
            if r[k] == x[l] {
                tempB := true;
            }
            if r[k] < x[l] {
                tangentMissing := true;
            }
            l := l + 1;
        }
        k := k + 1;
    }
    b := tempB;
}

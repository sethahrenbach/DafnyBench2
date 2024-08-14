
method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
{
    r := s;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant |r| == |s| + i
        invariant forall j :: 0 <= j < i ==> r[|s| + j] == a[j]
    {
        assert 0 <= i < a.Length;
        r := r + [a[i]];
        i := i + 1;
    }
}

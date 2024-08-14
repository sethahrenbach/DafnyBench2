
method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
    ensures |copy| == |s|
    ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
{
    var newSeq: seq<int> := [];
    for i := 0 to |s| - 1
        invariant |newSeq| == i
        invariant forall j :: 0 <= j < i ==> newSeq[j] == s[j]
    {
        newSeq := newSeq + [s[i]];
    }
    return newSeq;
}

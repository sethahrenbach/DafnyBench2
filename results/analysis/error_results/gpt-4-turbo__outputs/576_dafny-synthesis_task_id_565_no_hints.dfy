
method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
    v := [];
    var i := 0;
    while i < |s|
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> v[j] == s[j]
    {
        v := v + [s[i]];
        i := i + 1;
    }
}

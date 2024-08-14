method replace(v:array<int>, x:int, y:int)
    modifies v
    ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
    ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant forall k :: 0 <= k < i ==> (v[k] == x ==> v[k] == y) && (v[k] != x ==> v[k] == old(v[k]))
    {
        assert 0 <= i < v.Length;
        if v[i] == x {
            v[i] := y;
        }
        i := i + 1;
    }
}
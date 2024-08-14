method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{
    var oldV := new int[v.Length];
    var j := 0;
    while (j < v.Length)
        invariant 0 <= j <= v.Length
        invariant forall k::0 <= k < j ==> oldV[k] == v[k]
    {
        oldV[j] := v[j];
        j := j + 1;
    }

    var i := 0;
    while (i < v.Length)
        invariant 0 <= i <= v.Length
        invariant forall k::0 <= k < i && oldV[k] == x ==> v[k] == y
        invariant forall k::0 <= k < i && oldV[k] != x ==> v[k] == oldV[k]
        invariant forall k::i <= k < v.Length ==> v[k] == oldV[k]
    {
        if (v[i] == x) {
            v[i] := y;
        }
        i := i + 1;
    }
    assert forall k::0 <= k < v.Length && oldV[k] == x ==> v[k] == y;
    assert forall k::0 <= k < v.Length && oldV[k] != x ==> v[k] == oldV[k];
}
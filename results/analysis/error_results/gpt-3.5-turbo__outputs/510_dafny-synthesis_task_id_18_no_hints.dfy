
method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{
    var v' : string := [];
    var i := 0;
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant forall j :: 0 <= j < |v'| ==> (v'[j] in s1) && !(v'[j] in s2)
        invariant forall j :: i <= j < |s1| ==> (s1[j] in s2) || (s1[j] in v')
    {
        assert i <= |s1|;
        if !(s1[i] in s2)
        {
            v' := v' + [s1[i]];
        }
        i := i + 1;
    }
    assert i >= |s1|;
    assert |v'| <= |s1|;
    assert forall k :: 0 <= k < |v'| ==> (v'[k] in s1) && !(v'[k] in s2);
    assert forall k :: 0 <= k < |s1| ==> (s1[k] in s2) || (s1[k] in v');
    return v';
}

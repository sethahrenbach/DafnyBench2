predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
    var s' : string := "";
    var i : nat := 0;
    while i < |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (IsSpaceCommaDot(s[j]) ==> s'[j] == ':') && (!IsSpaceCommaDot(s[j]) ==> s'[j] == s[j])
    {
        if IsSpaceCommaDot(s[i])
        {
            s' := s' + ":";
        }
        else 
        {
            s' := s' + s[i];
        }
        i := i + 1;
    }
    return s';
}
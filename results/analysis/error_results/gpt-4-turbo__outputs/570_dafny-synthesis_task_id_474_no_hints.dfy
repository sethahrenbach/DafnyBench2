method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{
    var s' : string := "";
    var i: nat := 0;
    while i < |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (s[j] == oldChar ==> s'[j] == newChar) && (s[j] != oldChar ==> s'[j] == s[j])
    {
        if s[i] == oldChar
        {
            s' := s' + [newChar];
        }
        else 
        {
            s' := s' + [s[i]];
        }
        i := i + 1;
    }
    return s';
}
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    var s' : string := "";
    var i := 0;
    while i < |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (s[j] == ' ' ==> s'[j] == ch) && (s[j] != ' ' ==> s'[j] == s[j])
    {
        if s[i] == ' '
        {
            s' := s' + [ch];  // Correcting the concatenation by wrapping 'ch' in a list
        }
        else 
        {
            s' := s' + [s[i]];  // Correcting the concatenation by wrapping 's[i]' in a list
        }
        i := i + 1;
    }
    return s';
}
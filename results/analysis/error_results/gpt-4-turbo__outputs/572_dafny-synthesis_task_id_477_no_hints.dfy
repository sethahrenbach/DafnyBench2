predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := "";
    var i : nat := 0;
    while i < |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (IsUpperCase(s[j]) ==> IsUpperLowerPair(s[j], s'[j])) && (!IsUpperCase(s[j]) ==> s'[j] == s[j])
    {
        if IsUpperCase(s[i])
        {
            s' := s' + [Shift32(s[i])][0];
        }
        else 
        {
            s' := s' + [s[i]][0];
        }
        i := i + 1;
    }
    return s';
}
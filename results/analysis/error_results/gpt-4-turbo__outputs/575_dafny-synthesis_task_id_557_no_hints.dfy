predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := "";
    for i := 0 to |s| - 1
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (IsLowerCase(s[j]) ==> IsLowerUpperPair(s[j], s'[j])) || (IsUpperCase(s[j]) ==> IsUpperLowerPair(s[j], s'[j])) || (!IsLowerCase(s[j]) && !IsUpperCase(s[j]) ==> s'[j] == s[j])
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
        }
        else if IsUpperCase(s[i])
        {
            s' := s' + [Shift32(s[i])];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    v := s';
}
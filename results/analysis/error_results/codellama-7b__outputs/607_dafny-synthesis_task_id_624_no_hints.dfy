
predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    {
        // Loop invariant: s' is the result of converting the first i characters of s to uppercase
        // and the first (|s| - i) characters of s to lowercase
        // (Note: this is a stronger invariant than the one in the original program)
        loop invariant 0 <= i <= |s|
        loop invariant forall j :: 0 <= j < i ==> IsLowerCase(s[j])
        loop invariant forall j :: i <= j < |s| ==> IsLowerUpperPair(s[j], v[j])
        loop invariant forall j :: i <= j < |s| ==> v[j] == ShiftMinus32(s[j])
        
        if IsLowerCase(s[i])
        {
            // Assertion: the current character is lowercase
            assert IsLowerCase(s[i]);
            
            // Assertion: the converted character is uppercase
            assert IsLowerUpperPair(s[i], v[i]);
            
            s' := s' + [ShiftMinus32(s[i])];
        }
        else 
        {
            // Assertion: the current character is not lowercase
            assert !IsLowerCase(s[i]);
            
            // Assertion: the converted character is the same as the original character
            assert v[i] == s[i];
            
            s' := s' + [s[i]];
        }
    }
    return s';
}

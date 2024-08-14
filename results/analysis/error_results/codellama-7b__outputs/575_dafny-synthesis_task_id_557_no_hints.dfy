
function ToggleCase(s: string): string
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], result[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], result[i]) else result[i] == s[i]
{
    var result: string := "";
    for i := 0 to |s|
    {
        if IsLowerCase(s[i])
        {
            result := result + ShiftMinus32(s[i]);
        }
        else if IsUpperCase(s[i])
        {
            result := result + Shift32(s[i]);
        }
        else 
        {
            result := result + s[i];
        }
    }
    return result;
}

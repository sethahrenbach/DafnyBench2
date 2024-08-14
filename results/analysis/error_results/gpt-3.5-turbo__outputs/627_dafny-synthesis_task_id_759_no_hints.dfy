
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    result := false;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result ==> (exists j :: 0 <= j < i && s[j] == '.')
        invariant result ==> (|s| - i - 1 == 2)
    {
        if s[i] == '.' {
            if |s| - i - 1 == 2 {
                result := true;
                break;
            }
        }
        i := i + 1;
    }
}

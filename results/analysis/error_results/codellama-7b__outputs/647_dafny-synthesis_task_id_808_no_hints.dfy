
method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
    loop invariant 0 <= i <= |s|
    loop invariant result == (k in s)
{
    result := false;
    for i := 0 to |s|
    {
        if s[i] == k {
            result := true;
            break;
        }
    }
}

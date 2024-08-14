method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{
    result := false;
    var i := 0;
    while i < |s
        invariant 0 <= i <= |s
        invariant forall j :: 0 <= j < i ==> s[j] != k;
    {
        assert i <= |s;
        if s[i] == k {
            result := true;
            break;
        }
        i := i + 1;
    }
}
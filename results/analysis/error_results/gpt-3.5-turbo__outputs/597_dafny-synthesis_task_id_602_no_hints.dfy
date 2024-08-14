method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    requires |s| > 0
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    c := ' ';
    found := false;
    var inner_found := false;
    var i := 0;
    while i < |s| && !found
        invariant 0 <= i <= |s|
        invariant !found ==> (forall k :: 0 <= k < i ==> s[k] != c)
        invariant inner_found ==> exists j :: i <= j < |s| && s[i] == s[j] && s[i] == c
        invariant !inner_found ==> (forall j :: i <= j < |s| ==> s[j] != c)
    {
        var j := i + 1;
        while j < |s| && !inner_found
            invariant i <= j <= |s|
            invariant !inner_found ==> (forall k :: i <= k < j ==> s[k] != c)
        {
            if s[i] == s[j] {
                inner_found := true;
                c := s[i];
            }
            j := j + 1;
        }
        found := inner_found;
        i := i + 1;
    }
}
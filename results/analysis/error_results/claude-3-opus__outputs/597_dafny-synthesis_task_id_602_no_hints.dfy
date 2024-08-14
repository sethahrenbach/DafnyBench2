method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    c := ' ';
    found := false;
    var i := 0;
    while i < |s| && !found
        invariant 0 <= i <= |s|
        invariant !found ==> (forall ii, jj :: 0 <= ii < jj < i ==> s[ii] != s[jj])
        invariant found ==> exists ii, jj :: 0 <= ii < jj < i && s[ii] == s[jj] && s[ii] == c && (forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii)
    {
        var j := i + 1;
        var inner_found := false;
        while j < |s| && !inner_found 
            invariant i < j <= |s|
            invariant !inner_found ==> (forall jj :: i < jj < j ==> s[i] != s[jj])
            invariant inner_found ==> exists jj :: i < jj < j && s[i] == s[jj] && s[i] == c
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
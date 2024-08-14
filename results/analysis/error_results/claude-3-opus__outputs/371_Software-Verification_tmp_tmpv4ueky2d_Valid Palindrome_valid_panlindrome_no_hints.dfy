method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{
    var length := s.Length;
    result := true;

    var i := 0;
    while i < length / 2 
        invariant 0 <= i <= length / 2
        invariant forall j :: 0 <= j < i ==> s[j] == s[length - 1 - j]
        invariant result ==> forall k :: 0 <= k < i ==> s[k] == s[length - 1 - k]
    {
        if s[i] != s[length - 1 - i]
        {
            result := false;
            break;
        }

        i := i + 1;
    }
}
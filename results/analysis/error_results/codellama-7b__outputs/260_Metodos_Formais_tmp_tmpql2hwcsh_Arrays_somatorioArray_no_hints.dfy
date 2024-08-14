  I apologize for the mistake. Here is the corrected code:

method somatorio(a:array<nat>) returns (s:nat)
    ensures s == soma(a, a.Length)
{
    s := 0;
    for i := 0 to a.Length
    {
        s := s + a[i];
    }
}
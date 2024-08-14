method GetEven(s: array<nat>) modifies s
    ensures forall i :: 0 <= i < s.Length ==> 
                                if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1
                                else s[i] == old(s[i])
{
    var i := 0;
    while i < s.Length 
        invariant 0 <= i <= s.Length
        invariant forall j :: 0 <= j < i ==> 
                                if old(s[j]) % 2 == 1 then s[j] == old(s[j]) + 1
                                else s[j] == old(s[j])
    {
        assert 0 <= i < s.Length;
        if old(s[i]) % 2 == 1 {
            s[i] := old(s[i]) + 1;
        }
        else {
            assert old(s[i]) % 2 == 0;
            s[i] := old(s[i]);
        }
        i := i + 1;
    }
}

method evenTest()
{
    var a: array<nat> := new nat[](0, 9, 4);
    GetEven(a);
}
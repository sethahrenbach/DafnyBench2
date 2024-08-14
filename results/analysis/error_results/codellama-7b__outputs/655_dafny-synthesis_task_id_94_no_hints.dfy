
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{
    var minSecondIndex := 0;
    for i := 1 to s.Length
    {
        // Loop invariant: minSecondIndex is the index of the minimum second element in s[0..i]
        // Assertion: s[minSecondIndex][1] is the minimum second element in s[0..i]
        assert s[minSecondIndex][1] <= s[i][1];

        if s[i][1] < s[minSecondIndex][1]
        {
            // Loop invariant: minSecondIndex is the index of the minimum second element in s[0..i]
            // Assertion: s[minSecondIndex][1] is the minimum second element in s[0..i]
            assert s[minSecondIndex][1] <= s[i][1];
            minSecondIndex := i;
        }
    }
    // Loop invariant: minSecondIndex is the index of the minimum second element in s[0..s.Length]
    // Assertion: s[minSecondIndex][1] is the minimum second element in s[0..s.Length]
    assert s[minSecondIndex][1] <= s[s.Length][1];
    firstOfMinSecond := s[minSecondIndex][0];
}

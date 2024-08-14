
method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
{
    var minIndex := 0;
    var secondMinIndex := 1;

    // Loop Invariant: minIndex is the index of the minimum element in s
    // and secondMinIndex is the index of the second smallest element in s
    loop invariant 0 <= minIndex < s.Length;
    loop invariant 0 <= secondMinIndex < s.Length;
    loop invariant s[minIndex] <= s[secondMinIndex];

    // Assertion: s[minIndex] is the minimum element in s
    assert s[minIndex] == min(s[..]);

    // Assertion: s[secondMinIndex] is the second smallest element in s
    assert s[secondMinIndex] == secondSmallest;

    for i := 2 to s.Length
    {
        // Loop Invariant: minIndex is the index of the minimum element in s
        // and secondMinIndex is the index of the second smallest element in s
        loop invariant 0 <= minIndex < s.Length;
        loop invariant 0 <= secondMinIndex < s.Length;
        loop invariant s[minIndex] <= s[secondMinIndex];

        // Assertion: s[minIndex] is the minimum element in s
        assert s[minIndex] == min(s[..]);

        // Assertion: s[secondMinIndex] is the second smallest element in s
        assert s[secondMinIndex] == secondSmallest;

        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] < s[secondMinIndex] {
            secondMinIndex := i;
        }
    }

    secondSmallest := s[secondMinIndex];
}

method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{
    result := is_equal(multiset(s), multiset(t));
}

method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{
    var s_removed := multiset{};
    var s_remaining := s;
    while (|s_remaining| > 0)
        invariant |s_removed| + |s_remaining| == |s|
        invariant s_removed + s_remaining == s
        invariant s_removed <= s
        invariant s_remaining <= s
        invariant s_removed <= t
        invariant s_remaining + t == s + t - s_removed
        decreases |s_remaining|
    {
        var remaining :| remaining in s_remaining;
        assert remaining in s;
        assert remaining in t;
        assert s[remaining] == t[remaining];

        var temp := multiset{};
        s_removed := s_removed + temp[remaining := 1];
        s_remaining := s_remaining - temp[remaining := 1];
    }

    var t_removed := multiset{};
    var t_remaining := t;
    while (|t_remaining| > 0)
        invariant |t_removed| + |t_remaining| == |t|
        invariant t_removed + t_remaining == t
        invariant t_removed <= t
        invariant t_remaining <= t
        invariant t_removed <= s
        invariant t_remaining + s == t + s - t_removed
        decreases |t_remaining|
    {
        var remaining :| remaining in t_remaining;
        assert remaining in t;
        assert remaining in s;
        assert s[remaining] == t[remaining];

        var temp := multiset{};
        t_removed := t_removed + temp[remaining := 1];
        t_remaining := t_remaining - temp[remaining := 1];
    }

    return true;
}
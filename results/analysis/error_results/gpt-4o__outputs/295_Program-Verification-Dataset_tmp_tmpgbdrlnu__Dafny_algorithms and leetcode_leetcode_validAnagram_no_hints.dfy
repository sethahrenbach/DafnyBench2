method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant mset == multiset(s[0..i])
    {
        if i < |s| {
            assert multiset(s) == multiset(s[0..i]) + multiset{s[i]} + multiset(s[(i+1)..]);
            mset := mset + multiset{s[i]};
        }
    }
    assert mset == multiset(s[0..|s|]);
    return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    ghost var sremoved: multiset<char> := multiset{};
    var scopy := s;
    while scopy != multiset{}
        invariant s == scopy + sremoved
        invariant sremoved <= s
        invariant forall x :: x in sremoved ==> x in s
    {
        var x :| x in scopy;
        if !(x in t && s[x] == t[x]) {
            return false;
        }
        var removed := multiset{x};
        assert removed <= s;
        sremoved := sremoved + removed;
        scopy := scopy - removed;
    }
    assert scopy == multiset{};
    assert s - sremoved == scopy;
    assert sremoved == s;

    ghost var tremoved: multiset<char> := multiset{};
    var tcopy := t;
    while tcopy != multiset{}
        invariant t == tcopy + tremoved
        invariant tremoved <= t
        invariant forall x :: x in tremoved ==> x in t
    {
        var x :| x in tcopy;
        if !(x in s && s[x] == t[x]) {
            return false;
        }
        var removed := multiset{x};
        tremoved := tremoved + removed;
        tcopy := tcopy - removed;
    }
    assert forall x :: x in tremoved ==> x in t;

    return true;
}

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
    var smset := toMultiset(s);
    var tmset := toMultiset(t);
    equal := msetEqual(smset, tmset);
}
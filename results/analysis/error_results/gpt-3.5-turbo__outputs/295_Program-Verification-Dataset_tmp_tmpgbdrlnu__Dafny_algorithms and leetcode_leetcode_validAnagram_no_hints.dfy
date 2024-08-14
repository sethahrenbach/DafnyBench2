
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    var i := 0;
    while i < |s|
        invariant multiset(s) == mset + multiset(s[0..i]);
        decreases |s| - i;
    {
        mset := mset + multiset{s[i]};
        i := i + 1;
    }
    assert mset == multiset(s);
    return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    ghost var sremoved: multiset<char> := multiset{};
    var scopy := s;
    while scopy != multiset{}
        invariant scopy + sremoved == s;
        invariant forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x];
    {
        var x :| x in scopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{};
        assert removed[x := s[x]] <= s;
        sremoved := sremoved + removed[x := s[x]];
        scopy := scopy - removed[x := s[x]];
    }
    assert scopy == multiset{};
    assert sremoved == s;

    ghost var tremoved: multiset<char> := multiset{};
    var tcopy := t;
    while tcopy != multiset{}
        invariant tcopy + tremoved == t;
        invariant forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x];
    {
        var x :| x in tcopy;
        if !(x in s && t[x] == s[x]) {
           return false; 
        }
        var removed := multiset{};
        assert removed[x := t[x]] <= t;
        tremoved := tremoved + removed[x := t[x]];
        tcopy := tcopy - removed[x := t[x]];
    }
    assert tcopy == multiset{};
    assert tremoved == t;

    return true;
}

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
    var smset := toMultiset(s);
    var tmset := toMultiset(t);
    equal := msetEqual(smset, tmset);
}

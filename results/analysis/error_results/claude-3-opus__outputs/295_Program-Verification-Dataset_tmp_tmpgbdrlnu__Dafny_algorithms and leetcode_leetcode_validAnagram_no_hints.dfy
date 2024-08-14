method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant mset == multiset(s[0..i])
    {
        mset := mset + multiset{s[i]};
        i := i + 1;
    }
    assert i == |s|;
    assert mset == multiset(s[0..i]);
    assert s[0..i] == s;
    return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    ghost var sremoved: multiset<char> := multiset{};
    var scopy := s;
    while scopy != multiset{} 
        invariant scopy <= s
        invariant sremoved <= s
        invariant s == scopy + sremoved
        invariant forall x :: x in sremoved ==> x in t && t[x] == s[x]
    {
        var x :| x in scopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{x};
        assert removed[x := s[x]] <= s;
        sremoved := sremoved + removed;
        scopy := scopy - removed;
    }
    assert scopy == multiset{};
    assert s - sremoved == scopy;
    assert sremoved == s;
    assert forall x :: x in sremoved ==> x in t && t[x] == s[x];

    ghost var tremoved: multiset<char> := multiset{};
    var tcopy := t;
    while tcopy != multiset{} 
        invariant tcopy <= t
        invariant tremoved <= t
        invariant t == tcopy + tremoved
        invariant forall x :: x in tremoved ==> x in s && s[x] == t[x]
    {
        var x :| x in tcopy;
        if !(x in s && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{x};
        tremoved := tremoved + removed;
        tcopy := tcopy - removed;
    }
    assert forall x :: x in tremoved ==> x in s && s[x] == t[x];

    return true;
}

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
    var smset := toMultiset(s);
    var tmset := toMultiset(t);
    equal := msetEqual(smset, tmset);
}
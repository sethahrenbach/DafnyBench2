method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    var i := 0;
    while i < |s|
        invariant multiset(s[..i]) == mset
        invariant i <= |s|
    {
        mset := mset + multiset{s[i]};
        i := i + 1;
    }
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    ghost var sremoved: multiset<char> := multiset{};
    var scopy := s;
    while scopy != multiset{}
        invariant s == scopy + sremoved
        invariant forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x]
    {
        var x :| x in scopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{x := scopy[x]};
        sremoved := sremoved + removed;
        scopy := scopy - removed;
    }

    ghost var tremoved: multiset<char> := multiset{};
    var tcopy := t;
    while tcopy != multiset{}
        invariant t == tcopy + tremoved
        invariant forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x]
    {
        var x :| x in tcopy;
        if !(x in s && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{x := tcopy[x]};
        tremoved := tremoved + removed;
        tcopy := tcopy - removed;
    }

    return true;
}

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
    var smset := toMultiset(s);
    var tmset := toMultiset(t);
    equal := msetEqual(smset, tmset);
}
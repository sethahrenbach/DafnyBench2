// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{
    r := [];
    var rest := s;
    while rest != []
        invariant rest == s[|r|..];
        invariant IsSorted(r);
        invariant multiset(r) + multiset(rest) == multiset(s);
    {
        var x := rest[0];
        rest := rest[1..];
        var k := |r|;
        while k>0 && r[k-1]>x
            invariant 0 <= k <= |r|;
            invariant IsSorted(r);
            invariant multiset(r) + multiset(rest) == multiset(s);
        {
            r := r[..k]+[x]+r[k..];
            k := k-1;
            assert multiset(r) == multiset(r[..k]) + multiset([x]) + multiset(r[k..]);
            assert multiset(r) == multiset(s[0..|r|]) + multiset(s[|r|..]);
        }
        assert multiset(r) == multiset(s[0..|r|]) + multiset(s[|r|..]);
        assert multiset(r) == multiset(s);
        assert IsSorted(r);
    }
}
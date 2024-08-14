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
        invariant multiset(r + rest) == multiset(s)
        invariant IsSorted(r)
    {
        var x := rest[0];
        rest := rest[1..];
        var k := |r|;
        while k>0 && r[k-1]>x
            invariant 0 <= k <= |r|
            invariant multiset(r[..k] + r[k..]) == multiset(r)
            invariant IsSorted(r[..k]) && IsSorted(r[k..])
            invariant forall i | 0 <= i < k :: r[i] <= x
        {
            k := k-1;
        }
        r := r[..k]+[x]+r[k..];
        assert IsSorted(r[..k] + [x] + r[k..]);
        assert multiset(r[..k] + [x] + r[k..] + rest) == multiset(s);
    }
    assert multiset(r) == multiset(s);
    assert IsSorted(r);
}
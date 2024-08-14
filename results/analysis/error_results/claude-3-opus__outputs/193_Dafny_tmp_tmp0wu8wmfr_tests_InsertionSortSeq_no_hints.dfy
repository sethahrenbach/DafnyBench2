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
        invariant multiset(r) + multiset(rest) == multiset(s);
        invariant IsSorted(r);
    {
        var x := rest[0];
        rest := rest[1..];
        var k := |r|;
        while k>0 && r[k-1]>x
            invariant 0 <= k <= |r|;
            invariant forall i,j | 0 <= i < j < k :: r[i] <= r[j];
            invariant forall i | k <= i < |r| :: x <= r[i];
            decreases k;
        {
            k := k-1;
        }
        assert IsSorted(r[..k]);
        assert forall i | k <= i < |r| :: x <= r[i];
        assert k == 0 || r[k-1] <= x;
        r := r[..k]+[x]+r[k..];
        assert IsSorted(r[..k]+[x]);
        assert IsSorted([x]+r[k..]);
        assert forall i | 0 <= i < k :: r[i] <= x;
        assert forall i | k < i < |r| :: x <= r[i];
        assert k == 0 ==> IsSorted(r);
        assert k > 0 ==> r[k-1] <= x && IsSorted(r);
    }
}
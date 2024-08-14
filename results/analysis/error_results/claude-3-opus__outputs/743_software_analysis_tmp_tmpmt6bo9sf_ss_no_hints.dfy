method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s
ensures min_i >= s 
ensures min_i < e 
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
    min_i := s;
    var i : int := s + 1;  

    while i < e 
    invariant s <= min_i < i <= e
    invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    {
        if a[i] < a[min_i] {
            min_i := i;
        }
        i := i + 1;
    }
}

predicate is_sorted(ss: seq<int>)
{
    forall i, j: int:: 0 <= i <= j < |ss| ==> ss[i] <= ss[j]
}

predicate is_permutation(a:seq<int>, b:seq<int>)
{
    |a| == |b|  && 
    ((|a| == 0 && |b| == 0) ||  
    exists i,j : int :: 0<=i<|a| &&  0<=j<|b|  && a[i] == b[j] && is_permutation(a[0..i] + if i < |a| then a[i+1..] else [], b[0..j] + if j < |b| then  b[j+1..] else []))
}

predicate is_permutation2(a:seq<int>, b:seq<int>)
{
    multiset(a) == multiset(b)
}

lemma perm_trans(a: seq<int>, b: seq<int>, c: seq<int>)
requires is_permutation2(a, b)
requires is_permutation2(b, c)
ensures is_permutation2(a, c)
{
    assert multiset(a) == multiset(b);
    assert multiset(b) == multiset(c);
    assert multiset(a) == multiset(c);
}

lemma perm_swap(a: seq<int>, i: int, j: int)
requires 0 <= i < |a|
requires 0 <= j < |a|
ensures is_permutation2(a, a[i := a[j]][j := a[i]])
{
    assert multiset(a) == multiset(a[i := a[j]][j := a[i]]);
}

lemma sorted_after_swap(a: seq<int>, i: int, j: int)
requires 0 <= i < |a|
requires 0 <= j < |a|
requires is_sorted(a[..i])
requires is_sorted(a[i+1..])
requires forall k :: i < k < |a| ==> a[j] <= a[k]
ensures is_sorted(a[..i+1])
{
    if i > 0 {
        assert a[..i][i-1] <= a[j];
    }
}

method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
{
    var i: int := 0;
    var l: int := ns.Length;

    while i < l
    invariant 0 <= i <= l
    invariant is_sorted(ns[..i])
    invariant is_permutation2(old(ns[..]), ns[..])
    {
        var min_i: int := find_min_index(ns, i, l);
        ghost var old_ns := ns[..];
        ns[i], ns[min_i] := ns[min_i], ns[i];
        perm_swap(old_ns, i, min_i);
        assert is_permutation2(old_ns, ns[..]);
        assert forall k :: i < k < l ==> ns[i] <= ns[k];
        sorted_after_swap(ns[..], i, min_i);
        i := i + 1;
    }
}
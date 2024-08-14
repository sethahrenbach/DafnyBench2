method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
{
    if intSeq.Length <= 1 {
        return;
    }
    quickSortHelper(intSeq, 0, intSeq.Length - 1);
}

method quickSortHelper(intSeq:array<int>, lo:int, hi:int)
    modifies intSeq
    requires 0 <= lo <= hi < intSeq.Length
    ensures forall i:nat, j:nat | lo <= i <= j <= hi :: intSeq[i] <= intSeq[j]
    ensures multiset(intSeq[lo..hi+1]) == multiset(old(intSeq[lo..hi+1]))
{
    if lo < hi {
        var p := partition(intSeq, lo, hi);
        quickSortHelper(intSeq, lo, p - 1);
        quickSortHelper(intSeq, p + 1, hi);
    }
}

method partition(intSeq:array<int>, lo:int, hi:int) returns (p:int)
    modifies intSeq
    requires 0 <= lo <= hi < intSeq.Length
    ensures lo <= p <= hi
    ensures forall i:nat | lo <= i < p :: intSeq[i] <= intSeq[p]
    ensures forall i:nat | p < i <= hi :: intSeq[p] <= intSeq[i]
    ensures multiset(intSeq[lo..hi+1]) == multiset(old(intSeq[lo..hi+1]))
{
    var pivot := intSeq[hi];
    var i := lo;
    var j := lo;
    while j < hi
        invariant lo <= i <= j <= hi
        invariant multiset(intSeq[lo..hi+1]) == multiset(old(intSeq[lo..hi+1]))
        invariant forall k:nat | lo <= k < i :: intSeq[k] <= pivot
        invariant forall k:nat | i <= k < j :: intSeq[k] > pivot
    {
        if intSeq[j] <= pivot {
            intSeq[i], intSeq[j] := intSeq[j], intSeq[i];
            i := i + 1;
        }
        j := j + 1;
    }
    intSeq[i], intSeq[hi] := intSeq[hi], intSeq[i];
    return i;
}

lemma sort(prevSeq:seq<int>) returns (curSeq:seq<int>)
    ensures (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    ensures multiset(prevSeq) == multiset(curSeq)
{
    curSeq := prevSeq;
    curSeq := quickSortSeq(curSeq);
}

function quickSortSeq(seq: seq<int>): seq<int>
    ensures (forall i:nat, j:nat | 0 <= i <= j < |quickSortSeq(seq)| :: quickSortSeq(seq)[i] <= quickSortSeq(seq)[j])
    ensures multiset(seq) == multiset(quickSortSeq(seq))
{
    if |seq| <= 1 then seq
    else {
        var pivot := seq[|seq| / 2];
        var less := quickSortSeq([x | x <- seq, x < pivot]);
        var equal := [x | x <- seq, x == pivot];
        var greater := quickSortSeq([x | x <- seq, x > pivot]);
        less + equal + greater
    }
}

predicate post_sort(prevSeq:seq<int>, curSeq:seq<int>)
{
    (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j]) &&
    (multiset(prevSeq) == multiset(curSeq))
}

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
{
    assert m3 == m4;
}

lemma twoSortedSequencesWithSameElementsAreEqual(s1:seq<int>, s2:seq<int>)
    requires (forall i:nat, j:nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j])
    requires (forall i:nat, j:nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j])
    requires multiset(s1) == multiset(s2)
    requires |s1| == |s2|
    ensures s1 == s2
{
    if (|s1| != 0) {
        if s1[|s1|-1] == s2[|s1|-1] {
            multisetAdditivity(multiset(s1), multiset([s1[|s1|-1]]), multiset(s1[..|s1|-1]), multiset(s2[..|s1|-1]));
            twoSortedSequencesWithSameElementsAreEqual(s1[..|s1|-1], s2[..|s2|-1]);
        } else if s1[|s1|-1] < s2[|s1|-1] {
            assert false;
        } else {
            assert false;
        }
    }
}

lemma sort_deterministic(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
    if (|curSeq| != |curSeq'|) {
        assert false;
    } else {
        twoSortedSequencesWithSameElementsAreEqual(curSeq, curSeq');
    }
}

lemma sort_deterministic1(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires prevSeq == [5,4,3,2,1]
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
    sort_deterministic(prevSeq, curSeq, curSeq');
}

method quickSort(intSeq: array<int>)
    modifies intSeq
    ensures forall i: nat, j: nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
{
    var n := intSeq.Length;
    if (n > 1) {
        var pivot := intSeq[n / 2];
        var left := 0;
        var right := n - 1;

        while (left <= right) {
            while (left < n && intSeq[left] < pivot) {
                left := left + 1;
            }
            while (right >= 0 && intSeq[right] > pivot) {
                right := right - 1;
            }
            if (left <= right) {
                var temp := intSeq[left];
                intSeq[left] := intSeq[right];
                intSeq[right] := temp;
                left := left + 1;
                right := right - 1;
            }
        }
        assert forall i: nat, j: nat | 0 <= i <= j < left :: intSeq[i] <= intSeq[j];
        assert forall i: nat, j: nat | right < i <= j < n :: intSeq[i] <= intSeq[j];
        assert multiset(intSeq[..]) == multiset(old(intSeq[..]));

        quickSort(intSeq[0..right + 1]);
        quickSort(intSeq[left..n]);
    }
}

lemma sort(prevSeq: seq<int>) returns (curSeq: seq<int>)
    ensures forall i: nat, j: nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j]
    ensures multiset(prevSeq) == multiset(curSeq)
{
    curSeq := prevSeq;
    var i := 0;
    while (i < |curSeq| - 1) {
        var j := 0;
        invariant forall k: nat | 0 <= k < i :: forall l: nat | k <= l < |curSeq| :: curSeq[k] <= curSeq[l];
        invariant multiset(curSeq) == multiset(prevSeq);
        while (j < |curSeq| - i - 1) {
            if (curSeq[j] > curSeq[j + 1]) {
                var temp := curSeq[j];
                curSeq[j] := curSeq[j + 1];
                curSeq[j + 1] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

predicate post_sort(prevSeq: seq<int>, curSeq: seq<int>)
{
    (forall i: nat, j: nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    && multiset(prevSeq) == multiset(curSeq)
}

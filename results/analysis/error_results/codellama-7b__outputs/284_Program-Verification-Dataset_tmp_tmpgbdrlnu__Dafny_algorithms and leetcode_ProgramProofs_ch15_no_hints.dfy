
method QuickSort(a: array<int>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    if a.Length > 1 {
        var pivot := a[0];
        var lo := 0;
        var hi := a.Length - 1;
        while lo < hi {
            while lo < hi && a[hi] >= pivot {
                hi := hi - 1;
            }
            a[lo] := a[hi];
            lo := lo + 1;
            while lo < hi && a[lo] < pivot {
                lo := lo + 1;
            }
            a[hi] := a[lo];
            hi := hi - 1;
        }
        a[lo] := pivot;
        QuickSort(a[..lo]);
        QuickSort(a[lo+1..]);
    }
}


method swap(a: array<int>, i: nat, j: nat)
    modifies a
    requires a != null && a.Length > 0 && i < a.Length && j < a.Length
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{
    loop invariant a[i] == old(a[i]) && a[j] == old(a[j]) && a[i] == a[j] && a[j] == a[i];
    loop assigns a[i], a[j];
    loop variant j - i;
    a[i], a[j] := a[j], a[i];
}

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
    loop invariant a[lo..minIdx] <= a[lo..] && a[minIdx] <= a[lo] && a[lo..minIdx] <= a[lo..] && a[minIdx] <= a[lo];
    loop assigns minIdx;
    loop variant minIdx - lo;
    var j := lo;
    minIdx := lo;
    while j < a.Length
    {
        if(a[j] < a[minIdx]) { minIdx := j; }
        j := j + 1;
    }
}

method selectionSort(a: array<int>)
    modifies a
    //ensures multiset(a[..]) == multiset(old(a[..]))
    //ensures sorted(a[..])
{
    loop invariant forall i | 0 < i < a.Length :: a[i-1] <= a[i] && a[i] <= a[i+1] && a[i] <= a[i-1];
    loop assigns a[0..];
    loop variant a.Length;
    var i := 0;
    while(i < a.Length)
    {
        var mx := FindMin(a, i);
        //swap(a,i,mx);
        a[i], a[mx] := a[mx], a[i];
        i := i + 1;
    }
}

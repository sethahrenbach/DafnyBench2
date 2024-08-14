predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

method selSort (a:array<int>, c:int, f:int) //f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
    if (c <= f - 1) { //two elements at least
        var i := c;
        while (i < f - 1) //outer loop
        decreases f - i
        invariant c <= i <= f - 1
        invariant sorted_seg(a, c, i) || i == c
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        {
            var less := i;
            var j := i + 1;
            while (j < f) //inner loop
            decreases f - j
            invariant i + 1 <= j <= f
            invariant c <= i < f
            invariant less >= i && less < f
            invariant forall k :: i <= k < j ==> a[less] <= a[k]
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            {
                if (a[j] < a[less]) {
                    less := j;
                }
                j := j + 1;
            }
            a[i], a[less] := a[less], a[i];
            i := i + 1;
        }
        assert sorted_seg(a, c, f);
    }
}
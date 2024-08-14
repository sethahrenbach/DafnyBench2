twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    for i := 0 to a.Length - 1
    invariant 0 <= i <= a.Length
    invariant Ordered(a, 0, i)
    invariant Preserved(a, 0, a.Length)
    invariant forall k: nat :: 0 <= k < i ==> a[k] <= a[i]
    {
        var minValue := a[i];
        var minPos := i;
        for j := i + 1 to a.Length - 1
        invariant i <= j <= a.Length
        invariant minPos < a.Length
        invariant minValue == a[minPos]
        invariant forall k: nat :: i <= k <= j ==> a[minPos] <= a[k]
        {
            if a[j] < minValue {
                minValue := a[j];
                minPos := j;
            }
        }
        if i != minPos {
            a[i], a[minPos] := a[minPos], a[i];
        }
        assert Ordered(a, 0, i + 1);
    }
    assert Ordered(a, 0, a.Length);
}
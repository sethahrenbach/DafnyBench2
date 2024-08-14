
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
    forall i: nat :: left <= i < right ==> (i > 0 ==> a[i-1] <= a[i])
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    for i := 0 to a.Length - 1
    {
      var minValue := a[i];
      var minPos := i;
      for j := i + 1 to a.Length - 1
      {
        if j < a.Length && a[j] < minValue {
          minValue := a[j];
          minPos := j;
        }
      }
      if i != minPos {
        a[i], a[minPos] := minValue, a[i];
      }
    }
}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    for i := 0 to a.Length - 1
    {
      ghost var minValue := a[i];
      for j := i + 1 to a.Length - 1
      {
        label L:
        assert forall k: int :: i <= k < j ==> a[k] >= a[i];
        assert forall k: int :: i <= k < j ==> a[k] >= minValue;
        if j < a.Length && a[j] < minValue {
          minValue := a[j];
        }
        if j < a.Length && a[j] < a[i] {
            a[i], a[j] := a[j], a[i];
            assert Preserved(a, 0, a.Length);
        }else{
            assert Preserved(a, 0, a.Length);
        }
      }
    }
}

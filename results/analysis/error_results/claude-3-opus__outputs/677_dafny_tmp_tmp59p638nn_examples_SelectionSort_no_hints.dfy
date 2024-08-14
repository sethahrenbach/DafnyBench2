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
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
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
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant Ordered(a, 0, i)
        invariant Preserved(a, 0, a.Length)
    {
      var minValue := a[i];
      var minPos := i;
      for j := i + 1 to a.Length
        invariant i+1 <= j <= a.Length
        invariant minValue == a[minPos]
        invariant minPos == (if j > i+1 then (min k | i+1 <= k < j && a[k] == minValue :: k) else i)
        invariant Preserved(a, 0, a.Length)
      {
        if a[j] < minValue {
          minValue := a[j];
          minPos := j;
        }
      }
      if i != minPos {
        a[i], a[minPos] := minValue, a[i];
      }
      assert Ordered(a, 0, i+1);
    }
}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant Ordered(a, 0, i)
        invariant Preserved(a, 0, a.Length)
    {
      ghost var minValue := a[i];
      for j := i + 1 to a.Length
        invariant i+1 <= j <= a.Length
        invariant minValue == (if j > i+1 then (min k :: i+1 <= k < j ==> a[k]) else a[i])
        invariant Preserved(a, 0, a.Length)
      {
        label L:
        assert a[..] == a[0..a.Length];

        if a[j] < minValue {
          minValue := a[j];
        }
        if a[j] < a[i] {
            a[i], a[j] := a[j], a[i];
            assert Preserved(a, 0, a.Length);
        }else{
            assert Preserved(a, 0, a.Length);
        }
      }
      assert Ordered(a, 0, i+1);
    }
}
trait Comparable<T(==)> {
    function Lt(x: T, y: T): bool
}

trait Sorted<T(==)> extends Comparable<T> {

  ghost predicate Ordered(a: array<T>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
  {
    forall i: nat :: left <= i < right ==> (i == left || Lt(a[i-1],a[i]) || a[i-1] == a[i])
  }

  twostate predicate Preserved(a: array<T>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
  {
    multiset(a[left..right]) == multiset(old(a[left..right]))
  }

  twostate predicate Sorted(a: array<T>)
    reads a
  {
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
  }

}

class Sort<T(==)> extends SelectionSort<T> {
    const CMP: (T,T) -> bool

    constructor(cmp: (T,T) -> bool)
      ensures CMP == cmp
      ensures comparisonCount == 0
    {
      CMP := cmp;
      comparisonCount := 0;
    }

    function Lt(x: T, y: T): bool {
      CMP(x,y)
    }
}

ghost function Sum(x: int): nat
{
    if x <= 0 then 0 else x + Sum(x-1)
}

trait Measurable<T(==)> extends Comparable<T> {

    ghost var comparisonCount: nat

    method Ltm(x: T, y: T) returns (b: bool)
      modifies this`comparisonCount
      ensures b ==> Lt(x,y)
      ensures comparisonCount == old(comparisonCount) + 1
    {
      comparisonCount := comparisonCount + 1;
      b := Lt(x,y);
    }

}

trait SelectionSort<T(==)> extends Comparable<T>, Measurable<T>, Sorted<T> {

  method SelectionSort(a: array<T>)
    modifies a, this
    requires comparisonCount == 0
    ensures Sorted(a)
    ensures comparisonCount <= a.Length * a.Length
  {
    for i := 0 to a.Length - 2
      invariant Ordered(a,0,i+1)
      invariant Preserved(a,0,a.Length)
    {
      var minValue := a[i];
      var minPos := i;
      for j := i + 1 to a.Length - 1
      {
        label L:
        var cmp := Ltm(a[j], minValue);
        if cmp {
          minValue := a[j];
          minPos := j;
        }
      }
      if i != minPos {
        var temp := a[i];
        a[i] := a[minPos];
        a[minPos] := temp;
      }
    }
  }

}

method Main()
{
    var a: array<int> := new int[3];
    a[0] := 2; a[1] := 4; a[2] := 1;
    var Sort := new Sort((x: int, y: int) => x < y);
    Sort.SelectionSort(a);
    print a[..];
}

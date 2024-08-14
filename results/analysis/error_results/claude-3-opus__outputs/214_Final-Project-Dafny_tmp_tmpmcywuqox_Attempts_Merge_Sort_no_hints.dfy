method mergeSort(a: array<int>)
modifies a
{
  sorting(a, 0, a.Length-1);
}

method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
  var x := 0;
  var y := 0;
  var z := 0;
  var a1: array<int> := new [medium - low + 1];
  var a2: array<int> := new [high - medium];
  // The first case
  while(y < a1.Length)
    invariant 0 <= y <= a1.Length
    invariant low + y <= a.Length
    invariant forall i | 0 <= i < y :: a1[i] == old(a[low+i])
  {
    a1[y] := a[low+y];
    y := y +1;
  }
  // The second case
  while(z < a2.Length)
    invariant 0 <= z <= a2.Length
    invariant medium + z + 1 <= a.Length
    invariant forall i | 0 <= i < z :: a2[i] == old(a[medium+i+1])
  {
    a2[z] := a[medium+z+1];
    z := z +1;
  }
  y, z := 0, 0;
  // The third case
  while (x < high - low + 1)
    invariant 0 <= x <= high - low + 1
    invariant 0 <= y <= a1.Length
    invariant 0 <= z <= a2.Length
    invariant low + x <= a.Length
    invariant forall i | 0 <= i < x :: a[low+i] == if i < y then a1[i] else a2[i-y]
    invariant forall i,j | 0 <= i < j < y :: a1[i] <= a1[j]
    invariant forall i,j | 0 <= i < j < z :: a2[i] <= a2[j]
    invariant y == a1.Length ==> forall i | z <= i < a2.Length :: a2[i] <= if low+x < a.Length then a[low+x] else a[high]
    invariant z == a2.Length ==> forall i | y <= i < a1.Length :: a1[i] <= if low+x < a.Length then a[low+x] else a[high]
    invariant y < a1.Length && z < a2.Length ==> a1[y] <= a2[z]
  {
    if(y == a1.Length) {
      a[low+x] := a2[z];
      z := z+1;
    } else if(z == a2.Length) {
      a[low+x] := a1[y];
      y := y+1;
    } else {
      if(a1[y] <= a2[z]) {
        a[low+x] := a1[y];
        y := y +1;
      } else {
        a[low+x] := a2[z];
        z := z +1;
      }
    }
    x := x+1;
  }
}

method sorting(a: array<int>, low: int, high: int)
requires 0 <= low <= high < a.Length
modifies a
decreases high - low
{
    if (low < high) {
        var medium: int := low + (high - low)/2;
        sorting(a, low, medium);
        sorting(a, medium+1, high);
        merging(a, low, medium, high);
    }
}
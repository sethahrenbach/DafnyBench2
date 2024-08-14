predicate isSorted(a:array<int>)
  reads a
{
  forall i:nat, j:nat :: i <= j < a.Length ==> a[i] <= a[j]
}

method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
{
  var lo: nat := 0;
  var hi: nat := a.Length;
  while (lo < hi)
    invariant lo <= hi
    invariant forall j:nat :: j < lo ==> a[j] < K
    invariant forall j:nat :: hi <= j < a.Length ==> K < a[j]
    invariant 0 <= lo <= hi <= a.Length
  {
    var mid: nat = (lo + hi) / 2;
    if (a[mid] < K) {
      lo = mid + 1;
    } else if (a[mid] > K) {
      hi = mid;
    } else {
      return true;
    }
  }
  return false;
}
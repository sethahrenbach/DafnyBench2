
method isSorted(a: array<real>, from: nat, to: nat) returns(result: bool)
  requires 0 <= from < to <= a.Length
  ensures result == forall k :: from <= k < to ==> a[k] <= a[k+1]
{
  var i := from;
  while i < to - 1 {
    if a[i] > a[i+1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

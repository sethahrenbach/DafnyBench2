
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires a != null && 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  loop invariant 0 <= low <= high <= a.Length;
  loop invariant sorted(a[low..high]);
  loop invariant forall j :: 0 <= j < low ==> a[j] < value;
  loop invariant forall j :: high <= j < a.Length ==> value < a[j];
  loop assigns low, high;
  loop variant high - low;
  while low < high
    invariant 0 <= low <= high <= a.Length;
    invariant sorted(a[low..high]);
    invariant forall j :: 0 <= j < low ==> a[j] < value;
    invariant forall j :: high <= j < a.Length ==> value < a[j];
    invariant low <= i < high;
    invariant a[i] == value <==> i == index;
    invariant a[i] != value <==> i < 0;
    decreases high - low;
  {
    var mid := (low + high) / 2;
    if a[mid] < value
    {
      low := mid + 1;
    }
    else if value < a[mid]
    {
      high := mid;
    }
    else
    {
      return mid;
    }
  }
  return -1;
}

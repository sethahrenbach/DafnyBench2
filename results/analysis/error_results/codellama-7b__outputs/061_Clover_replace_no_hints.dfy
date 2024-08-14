
method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
{
  var i := 0;
  loop invariant 0 <= i <= arr.Length;
  loop invariant forall j :: 0 <= j < i ==> arr[j] == old(arr[j]);
  loop invariant forall j :: i <= j < arr.Length ==> arr[j] == old(arr[j]) || arr[j] == -1;
  loop assigns i, arr[0..i];
  while i < arr.Length
  {
    if arr[i] > k {
      arr[i] := -1;
    }
    i := i + 1;
  }
}

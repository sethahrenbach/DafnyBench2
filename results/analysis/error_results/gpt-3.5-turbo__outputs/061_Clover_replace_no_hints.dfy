
method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
{
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> (old(arr[j]) > k ==> arr[j] == -1) && (old(arr[j]) <= k ==> arr[j] == old(arr[j]))
  {
    if arr[i] > k {
      arr[i] := -1;
      assert arr[i] == -1;
    }
    else {
      assert arr[i] <= k;
    }
    i := i + 1;
  }
}

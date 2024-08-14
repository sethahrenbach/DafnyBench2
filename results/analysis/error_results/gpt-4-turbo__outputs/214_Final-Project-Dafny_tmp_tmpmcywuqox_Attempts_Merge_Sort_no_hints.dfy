method mergeSort(a: array<int>)
  modifies a
{
  sorting(a, 0, a.Length-1);
}

method merging(a: array<int>, low: int, medium: int, high: int)
  requires 0 <= low <= medium <= high < a.Length
  modifies a
{
  var n1 := medium - low + 1;
  var n2 := high - medium;
  var a1: array<int> := new int[n1];
  var a2: array<int> := new int[n2];

  var i := 0;
  var j := 0;
  var k := low;

  // Copy data to temp arrays
  while (i < n1)
    invariant 0 <= i <= n1
    invariant forall k :: 0 <= k < i ==> a1[k] == a[low+k]
  {
    a1[i] := a[low + i];
    i := i + 1;
  }

  while (j < n2)
    invariant 0 <= j <= n2
    invariant forall k :: 0 <= k < j ==> a2[k] == a[medium + 1 + k]
  {
    a2[j] := a[medium + 1 + j];
    j := j + 1;
  }

  i, j := 0, 0;

  // Merge the temp arrays back into a[low..high]
  while (i < n1 || j < n2)
    invariant 0 <= i <= n1
    invariant 0 <= j <= n2
    invariant low <= k <= high
    invariant forall l :: low <= l < k ==> a[l] <= a[k-1]
    decreases n1 + n2 - i - j
  {
    if (j >= n2 || (i < n1 && a1[i] <= a2[j])) {
      a[k] := a1[i];
      i := i + 1;
    } else {
      a[k] := a2[j];
      j := j + 1;
    }
    k := k + 1;
  }

  // Copy any remaining elements of a1, if there are any
  while (i < n1)
    invariant 0 <= i <= n1
    invariant k <= high
    invariant forall l :: low <= l < k ==> a[l] <= a[k-1]
    decreases n1 - i
  {
    a[k] := a1[i];
    i := i + 1;
    k := k + 1;
  }

  // Copy any remaining elements of a2, if there are any
  while (j < n2)
    invariant 0 <= j <= n2
    invariant k <= high
    invariant forall l :: low <= l < k ==> a[l] <= a[k-1]
    decreases n2 - j
  {
    a[k] := a2[j];
    j := j + 1;
    k := k + 1;
  }
}

method sorting(a: array<int>, low: int, high: int)
  requires 0 <= low && high < a.Length
  modifies a
{
  if (low < high) {
    var mid := low + (high - low) / 2;
    sorting(a, low, mid);
    sorting(a, mid + 1, high);
    merging(a, low, mid, high);
  }
}
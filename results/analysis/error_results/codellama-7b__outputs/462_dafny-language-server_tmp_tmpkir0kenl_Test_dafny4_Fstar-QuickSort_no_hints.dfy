
function mergeSort(A: array<int>, lo: int, hi: int): array<int>
  requires 0 <= lo <= hi < A.Length
  ensures 0 <= lo <= lo' <= hi' <= hi < A.Length
{
  if hi - lo < 1 then
    return A[lo..hi];
  else
  {
    var mid := (lo + hi) / 2;
    var left := mergeSort(A, lo, mid);
    var right := mergeSort(A, mid + 1, hi);
    return merge(left, right);
  }
}

function merge(left: array<int>, right: array<int>): array<int>
  requires 0 <= left.Length <= right.Length
  ensures 0 <= left.Length <= left'.Length <= right.Length <= right'.Length
{
  var result := new array<int>(left.Length + right.Length);
  var i := 0;
  var j := 0;
  while i < left.Length && j < right.Length
  {
    if left[i] <= right[j] then
    {
      result[i + j] := left[i];
      i := i + 1;
    }
    else
    {
      result[i + j] := right[j];
      j := j + 1;
    }
  }
  while i < left.Length
  {
    result[i + j] := left[i];
    i := i + 1;
  }
  while j < right.Length
  {
    result[i + j] := right[j];
    j := j + 1;
  }
  return result;
}

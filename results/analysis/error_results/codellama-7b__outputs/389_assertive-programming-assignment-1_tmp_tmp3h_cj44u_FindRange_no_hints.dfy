
method FindMax(arr: seq<int>) returns (max: int)
  ensures max >= 0
  ensures max < arr.Length
  ensures max == arr[max]
{
  var max := 0;
  for i := 0 to arr.Length - 1 {
    if arr[i] > max {
      max := arr[i];
    }
  }
  return max;
}


function sum(arr: seq<int>): int
  requires arr != null
  requires |arr| > 0
  ensures sum'result == sum(arr)
{
  var sum := 0;
  for i in arr
    sum := sum + i;
  return sum;
}

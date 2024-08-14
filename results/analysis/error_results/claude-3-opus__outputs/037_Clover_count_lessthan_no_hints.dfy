method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var remaining := numbers;

  while |remaining| > 0
    invariant remaining <= numbers
    invariant count == |set i | i in numbers - remaining && i < threshold|
    decreases |remaining|
  {
    var i :| i in remaining;
    remaining := remaining - {i};
    if i < threshold {
      count := count + 1;
    }
  }
}
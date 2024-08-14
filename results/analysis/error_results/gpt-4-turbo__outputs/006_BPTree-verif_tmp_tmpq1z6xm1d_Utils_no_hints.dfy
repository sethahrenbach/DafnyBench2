function SetLessThan(numbers: set<int>, threshold: int): set<int>
{
  set i | i in numbers && i < threshold
}

method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |SetLessThan(numbers, threshold)|
{
  count := 0;
  var ss := numbers;
  while ss != {}
    decreases |ss|
    invariant count == |SetLessThan(numbers - ss, threshold)|
  {
    var i: int :| i in ss;
    ss := ss - {i};
    if i < threshold {
      count := count + 1;
    }
  }
  assert count == |SetLessThan(numbers, threshold)|;
}

method Main()
{
  var s: set<int> := {1, 2, 3, 4, 5};
  var c: int := CountLessThan(s, 4);
  print c;
  assert c == 3;
}
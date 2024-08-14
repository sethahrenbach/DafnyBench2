iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant |xs| == i
    decreases 10 - i
  {
    x := start + i;
    yield;
    i := i + 1;
  }
}

method Main() {
  var i := new Gen(30);
  var m := i.MoveNext();
  while m
    decreases 10 - i
  {
    print i.x;
    m := i.MoveNext();
  }
}
iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 
    invariant 0 <= i <= 10
    invariant |xs| == i
    invariant i == |xs|
    decreases 10 - i
  {
    x := start + i;
    yield;
    i := i + 1;
  }
}

method Main() {
  var i := new Gen(30);
  while true
    decreases 10 - |i.xs|
  {
    var m := i.MoveNext();
    if (!m) {break; }
    assert 0 <= |i.xs| <= 10;
    assert i.x == 30 + |i.xs| - 1;
    print i.x;
  }
}
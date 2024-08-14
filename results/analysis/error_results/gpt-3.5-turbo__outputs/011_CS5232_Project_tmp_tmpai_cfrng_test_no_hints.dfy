iterator Gen(start: int) yields (x: int)
  requires start >= 0
  ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 invariant i >= 0 && i <= 10 {
    x := start + i;
    yield;
    i := i + 1;
  }
}

method Main() {
  var i := new Gen(30);
  while true
    invariant true
  {
    var m := i.MoveNext();
    if (!m) {break; }
    assert |i.xs| <= 10;
    assert i.x == 30 + |i.xs| - 1;
    print i.x;
  }
}
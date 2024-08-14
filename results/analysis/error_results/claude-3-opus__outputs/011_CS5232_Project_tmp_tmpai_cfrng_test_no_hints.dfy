iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 
    invariant 0 <= i <= 10
    invariant |xs| == i
    invariant forall j :: 0 <= j < |xs| ==> xs[j] == start + j
    decreases 10 - i
  {
    x := start + i;
    yield;
    i := i + 1;
  }
  assert |xs| == 10;
  assert forall j :: 0 <= j < |xs| ==> xs[j] == start + j;
}

method Main() {
  var i := new Gen(30);
  assert i.Valid();
  var index := 0;
  var more := i.MoveNext();
  while more
    invariant i.Valid()
    invariant 0 <= index <= 10
    invariant more <==> index < 10
    invariant |i.xs| == index
    invariant forall j :: 0 <= j < index ==> i.xs[j] == 30 + j
    decreases 10 - index
  {
    assert index < 10;
    assert i.x == 30 + index;
    print i.x;
    index := index + 1;
    more := i.MoveNext();
  }
  assert !more;
  assert index == 10;
  assert i.Valid();
  assert |i.xs| == 10;
  assert forall j :: 0 <= j < 10 ==> i.xs[j] == 30 + j;
}
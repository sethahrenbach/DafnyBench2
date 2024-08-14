method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var shrink := numbers;
  var grow := {};
  while |shrink| > 0
    invariant shrink + grow == numbers
    invariant grow <= numbers
    invariant count == |set i | i in grow && i < threshold|
    invariant shrink * grow == {}
    invariant |shrink| + |grow| == |numbers|
    invariant forall i :: i in grow ==> i in numbers
    invariant forall i :: i in shrink ==> i in numbers
    invariant forall i :: i in numbers ==> i in shrink || i in grow
    invariant forall i :: i in grow ==> i !in shrink
    invariant forall i :: i in numbers :: i in grow ==> (i < threshold ==> count >= 1)
  {
    var i: int :| i in shrink;
    shrink := shrink - {i};
    grow := grow + {i};
    if i < threshold {
      count := count + 1;
    }
  }
  assert grow == numbers;
  assert count == |set i | i in grow && i < threshold|;
}
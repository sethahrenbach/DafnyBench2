
method Main()
{
  test0(10);
  test5(11);
  test6(12);
  test1();
  test2();
}

predicate valid(x:int)
{
  x > 0
}

function ref1(y:int) : int
  requires valid(y);
{
  y - 1
}

lemma assumption1()
  ensures forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
{
}

method test0(a: int)
  requires valid(a);
{
  if ref1.requires(a) {
    ghost var b := ref1(a);
    assert valid(a); // ref1 requires valid(a)
    assert valid(b); // ref1 ensures valid(b)
    assert ref1(a) == ref1(b); // from assumption1
  }
}

method test5(a: int)
  requires valid(a);
{
  if valid(a) {
    assert valid(a); // valid(a) is the precondition of ref1
  }
}

method test6(a: int)
  requires valid(a);
{
  if ref1.requires(a) {
    assert valid(a); // the precondition of ref1 is valid(a)
    ghost var b := ref1(a);
    assert valid(b); // ref1 ensures valid(b)
    assert ref1(a) == ref1(b); // from assumption1
  }
}

method test1()
{
  assert forall a, b :: true ==> a == b;
}

function {:opaque} ref2(y:int) : int        // Now with an opaque attribute
  requires valid(y);
{
  y - 1
}

lemma assumption2()
  ensures forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
{
  reveal ref2();
}

method test2()
{
  assumption2();
  assert forall a, b :: true ==> a == b;
}

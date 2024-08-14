predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  1<i && (forall f :: 1 < f < i ==> !divides(f, i))
}

method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{
  var f := 2;
  while (f < i)
    invariant 2 <= f <= i
    invariant forall k :: 2 <= k < f ==> !divides(k, i)
  {
    if i % f == 0 {
      assert divides(f, i);
      assert !IsPrime(i);
      return false;
    }
    f := f + 1;
  }
  assert f == i;
  assert forall k :: 2 <= k < i ==> !divides(k, i);
  return true;
}

method Main()
{
  var a := test_prime(3);
  var b := test_prime(4);
  var c := test_prime(5);
}
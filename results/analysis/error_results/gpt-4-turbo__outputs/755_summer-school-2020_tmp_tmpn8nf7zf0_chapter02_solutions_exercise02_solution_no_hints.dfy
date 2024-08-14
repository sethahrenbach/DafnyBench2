predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}

method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{
  var f := 2;
  while (f < i)
    invariant 1 < f <= i
    invariant forall k :: 2 <= k < f ==> i % k != 0
  {
    if i % f == 0 {
      return false;
    }
    f := f + 1;
  }
  assert forall k :: 2 <= k < i ==> i % k != 0; // Assert that no divisors exist to satisfy the postcondition
  return true;
}

method Main()
{
  var a := test_prime(3);
  var b := test_prime(4);
  var c := test_prime(5);
}
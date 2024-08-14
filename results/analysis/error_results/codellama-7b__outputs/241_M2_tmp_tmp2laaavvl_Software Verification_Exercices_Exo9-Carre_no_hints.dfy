
method Carre(a: nat) returns (c: nat)
  ensures c == a*a
  decreases a
{
  var i := 0;
  c := 0;
  while i < a
  {
    // Loop invariant: c = a*a - (a-i)*(a-i)
    assert c == a*a - (a-i)*(a-i);
    c := c + 2*i +1;
    i := i + 1;
  }
  assert c == a*a;
}

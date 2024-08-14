
method M()
{
  // Loop Invariant: P()
  loop invariant P();

  // Precondition: P()
  requires P();

  // Postcondition: P()
  ensures P();

  N();
}

method N()
  ensures P();

predicate P()
{
  false
}

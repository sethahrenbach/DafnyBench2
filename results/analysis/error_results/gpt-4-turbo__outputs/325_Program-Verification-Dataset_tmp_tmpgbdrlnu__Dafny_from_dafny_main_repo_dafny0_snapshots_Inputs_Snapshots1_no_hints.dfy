method M()
{
  N();
}

method N()
  ensures P()
  decreases * // Indicates that this method may not terminate
{
  // The postcondition is inherently false, which is unsatisfiable.
  // Therefore, the method should never terminate normally.
  // We use a loop that never terminates to model this behavior.
  while (true) { }
}

predicate P()
{
  false
}
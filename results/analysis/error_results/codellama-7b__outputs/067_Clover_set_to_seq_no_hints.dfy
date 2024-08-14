
method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  // Loop Invariant: The elements in left are all distinct and not in xs.
  loop invariant multiset(left) == multiset(s) - multiset(xs);

  // Postcondition: The elements in s are all in xs.
  postcondition multiset(s) == multiset(xs);

  xs := [];
  var left: set<T> := s;
  while left != {}
  {
    // Assertion: The element x is in left.
    assert x in left;

    // Assertion: The element x is not in xs.
    assert x not in xs;

    left := left - {x};
    xs := xs + [x];
  }
}

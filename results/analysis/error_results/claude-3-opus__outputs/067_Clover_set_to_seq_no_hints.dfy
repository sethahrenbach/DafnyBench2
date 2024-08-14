method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var left := s;
  while left != {}
    invariant left <= s
    invariant multiset(xs) + multiset(left) == multiset(s)
    invariant |xs| + |left| == |s|
    invariant forall x :: x in xs ==> x !in left
    decreases |left|
  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
    assert multiset(xs) + multiset(left) == multiset(s);
    assert |xs| + |left| == |s|;
    assert forall x :: x in xs ==> x !in left;
  }
}
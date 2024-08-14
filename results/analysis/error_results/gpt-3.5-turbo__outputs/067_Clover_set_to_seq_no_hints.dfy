method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var left: set<T> := s;
  while left != {}
    invariant forall x :: x in xs ==> x in s
    invariant forall x :: x in left ==> x in s
    invariant multiset(s) == multiset(xs + xs + SetToSeq(left))
  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
  }
}
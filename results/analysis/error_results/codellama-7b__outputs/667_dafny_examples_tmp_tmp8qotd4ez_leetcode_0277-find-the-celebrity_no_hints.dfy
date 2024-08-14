
method findCelebrity(n : int) returns (r : int)
  requires 2 <= n <= 100;
  ensures 0 <= r < n ==> isCelebrity(n, r);
  ensures r == -1 ==> forall i :: 0 <= i < n ==> !isCelebrity(n, i);
{
  var candidate := 0;
  var i := 1;
  while i < n
  {
    if knows(candidate, i)
    {
      candidate := i;
    }
    i := i + 1;
  }
  var isCelebrityC := isCelebrityP(n, candidate);
  if isCelebrityC
  {
    r := candidate;
  }
  else
  {
    r := -1;
  }
}

predicate isCelebrity(n : int, i : int)
  requires 0 <= i < n;
{
  forall j :: 0 <= j < n && i != j ==> knows(j, i) && !knows(i, j);
}

predicate isCelebrityP(n : int, i : int)
  requires 0 <= i < n;
{
  exists j :: 0 <= j < n && i != j && knows(j, i) && !knows(i, j);
}


method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures IsSorted(output)
  ensures multiset(output) == multiset(a + b)
  decreases |a| + |b|
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
  {
    if ai == |a| || (bi < |b| && a[ai] > b[bi])
    {
      output := output + [b[bi]];
      bi := bi + 1;
    }
    else
    {
      output := output + [a[ai]];
      ai := ai + 1;
    }
  }
  return output;
}

function IsSorted(s:seq<int>):bool
  requires s != null
{
  var i := 0;
  while i < |s| - 1
  {
    if s[i] > s[i + 1]
      return false;
    i := i + 1;
  }
  return true;
}

method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
{
  if |x| == 0 {
    return true;
  }
  var i := 0;
  var j := |x| - 1;
  while (i < j)
    invariant 0 <= i <= j < |x|
    invariant j == |x| - i - 1
    invariant forall k :: 0 <= k < i ==> x[k] == x[|x| - k - 1]
    invariant forall k :: i <= k <= j ==> x[k] == x[|x| - k - 1]
  {
    if x[i] != x[j] {
      return false;
    }
    i := i + 1;
    j := j - 1;
  }
  return true;
}
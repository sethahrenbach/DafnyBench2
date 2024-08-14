
function IsPalindrome(s: string): bool
{
  var i := 0;
  var j := |s| - 1;
  while i < j {
    if s[i] != s[j] {
      return false;
    }
    i := i + 1;
    j := j - 1;
  }
  return true;
}

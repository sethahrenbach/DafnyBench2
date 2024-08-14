
method length(s: seq<char>) returns (n: nat)
  requires s != null
  ensures n == s.Length
{
  var i := 0;
  while i < s.Length {
    if s[i] == '\n' {
      n := n + 1;
    }
    i := i + 1;
  }
  return n;
}

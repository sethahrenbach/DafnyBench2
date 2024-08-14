
method Parse(input: seq<char>) returns (result: seq<char>)
  requires input != null;
  requires input.Length > 0;
  ensures result != null;
  ensures result.Length > 0;
{
  var i := 0;
  var j := 0;
  while i < input.Length {
    if input[i] == '(' {
      j := i;
      while j < input.Length && input[j] != ')' {
        j := j + 1;
      }
      if j < input.Length {
        result := input[j + 1..];
      }
    }
    i := i + 1;
  }
  return result;
}


method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{
  var minLength := if |str1| <|str2| then |str1| else |str2|;
  var idx := 0;
  while idx < minLength && str1[idx] == str2[idx] {
    prefix := prefix + [str1[idx]];
    idx := idx + 1;
  }
  return prefix;
}

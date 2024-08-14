
method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|] && |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || (str1[|prefix|] != str2[|prefix|])
{
  prefix := [];
  var minLength := if |str1| < |str2| then |str1| else |str2|;

  var idx := 0;
  while idx < minLength
    invariant 0 <= idx <= minLength
    invariant |prefix| <= |str1| && prefix == str1[0..|prefix|] && |prefix| <= |str2| && prefix == str2[0..|prefix|]
    invariant |prefix| <= idx
    decreases minLength - idx
  {
    assert 0 <= idx < |str1| && 0 <= idx < |str2|;
    if str1[idx] != str2[idx] {
      assert |prefix| <= |str1| && prefix == str1[0..|prefix|] && |prefix| <= |str2| && prefix == str2[0..|prefix|];
      assert |prefix| == |str1| || |prefix| == |str2| || (str1[|prefix|] != str2[|prefix|]);
      return;
    }
    prefix := prefix + [str1[idx]];
    idx := idx + 1;
  }
  assert |prefix| <= |str1| && prefix == str1[0..|prefix|] && |prefix| <= |str2| && prefix == str2[0..|prefix|];
  assert |prefix| == |str1| || |prefix| == |str2| || (str1[|prefix|] != str2[|prefix|]);
}

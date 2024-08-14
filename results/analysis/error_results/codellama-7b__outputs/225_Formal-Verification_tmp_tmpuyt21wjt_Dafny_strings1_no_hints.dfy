
method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  ensures len <= |str1| && len <= |str2|
  ensures len >= 0
  ensures maxCommonSubstringPredicate(str1, str2, len)
{
  var i := 0;
  while i < |str1| {
    var j := 0;
    while j < |str2| {
      if str1[i] == str2[j] {
        j := j + 1;
      } else {
        j := 0;
      }
      i := i + 1;
    }
    if j == |str2| {
      return i;
    }
  }
  return 0;
}

predicate maxCommonSubstringPredicate(str1: string, str2: string, len: nat)
{
  forall k :: 0 <= k < len ==> isSubstringPredicate(str1[k..], str2[k..]);
}

predicate isSubstringPredicate(sub: string, str: string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]));
}

predicate isPrefixPredicate(pre: string, str: string)
{
  |str| >= |pre| && pre <= str;
}

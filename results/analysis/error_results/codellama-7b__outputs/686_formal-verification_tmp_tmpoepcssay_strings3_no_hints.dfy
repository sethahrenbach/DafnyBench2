
method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  requires |str1| <= |str2|
  ensures len <= |str1|
  ensures len <= |str2|
  ensures len <= |str1| && len <= |str2| ==> haveCommonKSubstring(len, str1, str2)
{
  len := |str1|;
  var hasCommon : bool := true;
  while (len > 0 && hasCommon)
  {
    hasCommon := haveCommonKSubstring(len, str1, str2);
    if (!hasCommon)
    {
      len := len - 1;
    }
  }
  return len;
}

function haveCommonKSubstring(k: nat, str1: string, str2: string): bool
  requires k <= |str1| && k <= |str2|
  ensures k <= |str1| && k <= |str2| ==> haveCommonKSubstring(k, str1, str2)
{
  var i := 0;
  var j := 0;
  while (i < |str1| - k + 1 && j < |str2| - k + 1)
  {
    if (str1[i..i+k] == str2[j..j+k])
    {
      return true;
    }
    i := i + 1;
    j := j + 1;
  }
  return false;
}

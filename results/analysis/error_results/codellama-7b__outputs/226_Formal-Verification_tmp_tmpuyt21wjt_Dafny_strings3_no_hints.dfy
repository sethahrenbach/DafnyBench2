
method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  requires (|str1| <= |str2|)
  ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstring(k, str1, str2))
  ensures haveCommonKSubstring(len, str1, str2)
{
  var i := |str1|;

  while i > 0
  {
    var ans := haveCommonKSubstring(i, str1, str2);
    if ans {
      return i;
    }
    i := i -1;
  }
  return 0;
}

predicate haveCommonKSubstring(k: nat, str1: string, str2: string)
{
  exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstring(str1[i1..j1], str2)
}

predicate isSubstring(sub: string, str: string)
{
  (exists i :: 0 <= i <= |str| && isPrefix(sub, str[i..]))
}

predicate isPrefix(pre: string, str: string)
{
  (|pre| <= |str|) && pre == str[..|pre|]
}

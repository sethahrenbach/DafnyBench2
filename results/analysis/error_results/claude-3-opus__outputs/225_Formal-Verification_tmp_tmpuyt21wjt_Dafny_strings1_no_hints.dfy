predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str|
    {return false;}

  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
  {
    if pre[i] != str[i]
    {
        return false;
    } 
    i := i + 1;
  }
  assert i == |pre|;
  assert forall j :: 0 <= j < |pre| ==> pre[j] == str[j];
  return true;
}

predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| - |sub| && isPrefixPredicate(sub, str[i..]))
}

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
    if |sub| > |str| {
        return false;
    }

    var i := |str| - |sub|;
    while i >= 0 
      invariant -1 <= i <= |str| - |sub|
      invariant forall j :: i < j <= |str| - |sub| ==> !isPrefixPredicate(sub, str[j..])
    {
        var isPref := isPrefix(sub, str[i..]);
        if isPref
        {
            return true;
        }
        i := i-1;
    }
    assert i == -1;
    assert forall j :: 0 <= j <= |str| - |sub| ==> !isPrefixPredicate(sub, str[j..]);
    return false;
}

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}


method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
    if( |str1| < k || |str2| < k){
        return false;
    }
    var i := |str1| - k;
    while i >= 0
      invariant -1 <= i <= |str1| - k
      invariant forall j :: i < j <= |str1| - k ==> !isSubstringPredicate(str1[j..][..k], str2)
    {
        var isSub := isSubstring(str1[i..][..k], str2);
        if isSub 
        {
            return true;
        }
        i := i-1;
    }
    assert i == -1;
    assert forall j :: 0 <= j <= |str1| - k ==> !isSubstringPredicate(str1[j..][..k], str2);
    return false;
}


predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   haveCommonKSubstringPredicate(len, str1, str2) && 
   forall k :: len < k <= |str1| && len < k <= |str2| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{
  var shorter := if |str1| < |str2| then |str1| else |str2|;
  var i := shorter;

  while i > 0
    invariant 0 <= i <= shorter
    invariant forall j :: i <= j <= shorter ==> !haveCommonKSubstringPredicate(j, str1, str2)
    invariant forall j :: 0 <= j < i ==> |str1| >= j && |str2| >= j
  {
    var ans := haveCommonKSubstring(i, str1, str2);
    if ans {
       return i;
    }
    i := i -1;
  }
  assert i == 0;
  assert forall j :: 1 <= j <= shorter ==> !haveCommonKSubstringPredicate(j, str1, str2);
  return 0;
}
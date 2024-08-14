// We spent 2h each on this assignment

predicate isPrefixPred(pre:string, str:string)
{
    (|pre| <= |str|) && 
    pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
    (|pre| > |str|) || 
    pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
    ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
    ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
    if |pre| > |str| {
        return false;
    }

    var i := 0;
    while i < |pre|
    invariant 0 <= i <= |pre|
    invariant pre[..i] == str[..i]
    {
        if pre[i] != str[i] {
            return false;
        } 
        i := i + 1;
    }
    return true;
}

predicate isSubstringPred(sub:string, str:string)
{
    exists i | 0 <= i < |str| - |sub| + 1 :: isPrefixPred(sub, str[i..])
}

predicate isNotSubstringPred(sub:string, str:string)
{
    forall i | 0 <= i < |str| - |sub| + 1 :: isNotPrefixPred(sub, str[i..])
}

lemma SubstringNegationLemma(sub:string, str:string)
    ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
    ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
{
    if |sub| > |str| {
        return false;
    }

    var i := |str| - |sub|;
    while i >= 0 
    invariant 0 <= i <= |str| - |sub|
    invariant forall j | i < j <= |str| - |sub| :: !isPrefixPred(sub, str[j..])
    {
        var isPref := isPrefix(sub, str[i..]);
        if isPref {
            return true;
        }
        i := i-1;
    }
    return false;
}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i1 | 0 <= i1 <= |str1|-k :: isSubstringPred(str1[i1..i1+k], str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i1 | 0 <= i1 <= |str1|-k :: isNotSubstringPred(str1[i1..i1+k], str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
    ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
    ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
{
    if |str1| < k || |str2| < k {
        return false;
    }
    var i := 0;
    while i <= |str1| - k
    invariant 0 <= i <= |str1| - k
    invariant forall j | 0 <= j < i :: !isSubstringPred(str1[j..j+k], str2)
    {
        var isSub := isSubstring(str1[i..i+k], str2);
        if isSub {
            return true;
        }
        i := i + 1;
    }
    return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires |str1| <= |str2|
    ensures (forall k | len < k <= |str1| :: !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
{
    var i := |str1|;
    while i > 0
    invariant 0 <= i <= |str1|
    invariant forall k | i < k <= |str1| :: !haveCommonKSubstringPred(k, str1, str2)
    {
        var ans := haveCommonKSubstring(i, str1, str2);
        if ans {
            return i;
        }
        i := i - 1;
    }
    return 0;
}
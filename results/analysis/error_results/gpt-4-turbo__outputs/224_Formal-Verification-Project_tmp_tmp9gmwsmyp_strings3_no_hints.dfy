
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
    if |str| < |pre| 
    {
        return false;
    }
    else if pre[..] == str[..|pre|]
    {
        return true;
    }
    else{
        return false;
    }
}

predicate isSubstringPred(sub:string, str:string)
{
    exists i | 0 <= i < |str| :: isPrefixPred(sub, str[i..])
}

predicate isNotSubstringPred(sub:string, str:string)
{
    forall i | 0 <= i < |str| :: isNotPrefixPred(sub, str[i..])
}

lemma SubstringNegationLemma(sub:string, str:string)
    ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
    ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
{
    var i := 0;
    res := false;
    while i < |str|
        invariant 0 <= i <= |str|
        invariant res <==> (exists j | 0 <= j < i :: isPrefixPred(sub, str[j..]))
    {
        var temp := isPrefix(sub, str[i..]);
        if temp == true 
        {
            res := true;
            break;
        }
        i := i + 1;
    } 
    return res;
}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i1 | 0 <= i1 <= |str1|- k :: isSubstringPred(str1[i1..i1+k],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i1 | 0 <= i1 <= |str1|- k :: isNotSubstringPred(str1[i1..i1+k],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
    ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
    ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
{
    if (k > |str1| || k > |str2| ){
        return false;
    }
    var i := 0;
    found := false;
    while i <= |str1|-k
        invariant 0 <= i <= |str1| - k
        invariant found <==> (exists j | 0 <= j <= i :: isSubstringPred(str1[j..j+k], str2))
    {
        found := isSubstring(str1[i..i+k], str2);
        if found == true 
        {
            break;
        }
        i := i + 1;
    }
    return found;
}

lemma haveCommon0SubstringLemma(str1:string, str2:string)
    ensures  haveCommonKSubstringPred(0,str1,str2)
{
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires |str1| <= |str2|
    ensures (forall k | len < k <= |str1| :: !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
{
    var temp := false;
    var i := |str1|;
    len := i;
    while i >= 0
        invariant 0 <= i <= |str1|
        invariant temp <==> haveCommonKSubstringPred(i, str1, str2)
    {
        temp := haveCommonKSubstring(i, str1, str2);
        if temp == true
        { 
            len := i;
            break;
        }
        i := i - 1;
    }
    haveCommon0SubstringLemma(str1, str2);
    return len;
}

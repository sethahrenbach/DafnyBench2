function IsLetter(c: char): bool 
{
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') 
}

function NoLetters(s: string, n: nat): bool 
  requires n <= |s|
{
  forall c :: 0 <= c < n ==> !IsLetter(s[c])
}

function ToggleCase(c: char): char
{
  if c >= 'a' && c <= 'z' 
  then 
    (c - 'a' + 'A')
  else if c >= 'A' && c <= 'Z' 
    then 
      (c - 'A' + 'a')
    else 
      c
}

function isReverse(s: string, s_prime: string): bool{
  (|s| == |s_prime|) &&
  (forall si :: 0 <= si < |s| ==> s_prime[|s| - si - 1] == s[si])
}

method Reverse(original: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |original| 
  ensures forall i :: 0 <= i < |original| ==> reversed[i] == original[|original| - 1 - i] 
{
  reversed := []; 
  var i := |original|;
  while i > 0
    invariant 0 <= i <= |original|
    invariant |reversed| == |original| - i
    invariant forall j :: 0 <= j < |reversed| ==> reversed[j] == original[|original| - 1 - j]
  {
    i := i - 1;
    reversed := reversed + [original[i]]; 
  }
}

method solve(s: string) returns (result: string)
  ensures |result| == |s| 
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && IsLetter(s[i]) ==> result[i] == ToggleCase(s[i])
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && !IsLetter(s[i]) ==> result[i] == s[i] 
  ensures NoLetters(s, |s|) ==> isReverse(result, s) 
{
    var flg : bool := false;
    result := "";
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant |result| == i
      invariant flg ==> !NoLetters(s, i)
      invariant !flg ==> NoLetters(s, i)
      invariant forall j :: 0 <= j < i && IsLetter(s[j]) ==> result[j] == ToggleCase(s[j])
      invariant forall j :: 0 <= j < i && !IsLetter(s[j]) ==> result[j] == s[j]
    {
      if IsLetter(s[i])
      {
        result := result + [ToggleCase(s[i])];
        flg := true;
      } else {
        result := result + [s[i]];
      }
      i := i + 1;
    }
    if !flg
    {
      var revSeq := Reverse(s.ToCharArray());
      result := "";
      var j := 0;
      while j < |revSeq|
        invariant 0 <= j <= |revSeq|
        invariant |result| == j
        invariant forall k :: 0 <= k < j ==> result[k] == revSeq[k]
      {
        result := result + [revSeq[j]];
        j := j + 1;
      }
    }
}
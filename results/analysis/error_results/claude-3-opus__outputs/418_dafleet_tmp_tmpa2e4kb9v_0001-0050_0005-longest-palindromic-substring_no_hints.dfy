/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s[i..j]` is palindromic
ghost predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

// A "common sense" about palindromes:
lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s, lo, hi)
  ensures palindromic(s, lo', hi')
  decreases hi - lo
{
  if lo < lo' {
    lemma_palindromic_contains(s, lo + 1, hi - 1, lo', hi');
  }
}

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)  // Among all palindromes
    && i + j == i0 + j0                                             // sharing the same center,
    :: j - i <= hi - lo                                             // `s[lo..hi]` is longest.
{
  lo, hi := i0, j0;

  // we try expanding whenever possible:
  while lo - 1 >= 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= i0 <= j0 <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 :: j - i <= hi - lo
    decreases |s| - hi, lo
  {
    lo, hi := lo - 1, hi + 1;
  }

  // proves that we cannot go further:
  forall i, j | 0 <= i <= lo && hi <= j <= |s| && i + j == i0 + j0 && j - i > hi - lo ensures !palindromic(s, i, j) {
    if palindromic(s, i, j) { // prove by contradiction:
      lemma_palindromic_contains(s, i, j, lo - 1, hi + 1);
      assert false;
    }
  }
}


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]  // `ans` is indeed a substring in `s`
  ensures palindromic(s, lo, hi)  // `ans` is palindromic
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo  // `ans` is longest
{
  lo, hi := 0, 0;
  for k := 0 to |s|
    invariant 0 <= lo <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j < 2*k :: j - i <= hi - lo
  {
    if k < |s| {
      var a, b := expand_from_center(s, k, k);
      if b - a > hi - lo {
        lo, hi := a, b;
      }
      var c, d := expand_from_center(s, k, k + 1);
      if d - c > hi - lo {
        lo, hi := c, d;
      }
    }
  }
  return s[lo..hi], lo, hi;
}

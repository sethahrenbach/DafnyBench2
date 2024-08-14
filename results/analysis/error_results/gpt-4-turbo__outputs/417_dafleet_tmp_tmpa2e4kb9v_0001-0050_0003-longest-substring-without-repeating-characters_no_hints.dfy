
/* https://leetcode.com/problems/longest-substring-without-repeating-characters/
Given a string s, find the length of the longest substring without repeating characters.

Example 1:
Input: s = "abcabcbb"
Output: 3
Explanation: The answer is "abc", with the length of 3.
*/

// a left-inclusive right-exclusive interval:
type interval = iv: (int, int) | iv.0 <= iv.1 witness (0, 0)

ghost function length(iv: interval): int {
  iv.1 - iv.0
}

ghost predicate valid_interval(s: string, iv: interval) {
  && (0 <= iv.0 <= iv.1 <= |s|)                             // interval is in valid range
  && (forall i, j | iv.0 <= i < j < iv.1 :: s[i] != s[j])   // no repeating characters in interval
}

// Below shows an efficient solution using standard "sliding window" technique. 
// For verification simplicity, we pretend as if:
// - `set` were Python set (or even better, a fixed-size array -- if the "alphabet" is small)
//
// `best_iv` is for verification purpose, not returned by the real program, thus `ghost`.
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n    /** `best_iv` is valid */
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n  /** `best_iv` is longest */
{
  var lo, hi := 0, 0;             // initialize the interval [lo, hi)
  var char_set: set<char> := {};  // `char_set` stores all chars within the interval
  n, best_iv := 0, (0, 0);        // keep track of the max length and corresponding interval

  while hi < |s|
    invariant lo <= hi <= |s|
    invariant valid_interval(s, (lo, hi))
    invariant char_set == set s[lo..hi]
    invariant forall k | lo <= k < hi :: s[k] in char_set
    invariant forall k | k in char_set ==> (exists j | lo <= j < hi && s[j] == k)
    invariant n == length(best_iv) && valid_interval(s, best_iv)
    invariant forall iv | valid_interval(s, iv) && iv.1 <= hi :: length(iv) <= n
  {
    if s[hi] !in char_set {  // sliding `hi` to lengthen the interval:
      char_set := char_set + {s[hi]};
      hi := hi + 1;
      if hi - lo > n {  // update the max length: 
        n := hi - lo;
        best_iv := (lo, hi);
      }
    } else {  // sliding `lo` to shorten the interval: 
      char_set := char_set - {s[lo]};
      lo := lo + 1;
    }
  }
}

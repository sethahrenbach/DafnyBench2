
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The RoundDown and RoundUp methods in this file are the ones in the Boogie
// implementation Source/AbsInt/IntervalDomain.cs.

class Rounding {
  var thresholds: array<int>

  function Valid(): bool
    reads this, thresholds
    ensures forall m,n :: 0 <= m < n < thresholds.Length ==> thresholds[m] <= thresholds[n]
  {
    true
  }

  method RoundDown(k: int) returns (r: int)
    requires Valid()
    ensures -1 <= r < thresholds.Length
    ensures forall m :: r < m < thresholds.Length ==> k < thresholds[m]
    ensures 0 <= r ==> thresholds[r] <= k
  {
    if (thresholds.Length == 0 || k < thresholds[0]) {
      return -1;
    }
    var i, j := 0, thresholds.Length;
    while (i < j)
      invariant 0 <= i <= j <= thresholds.Length
      invariant i < thresholds.Length ==> thresholds[i] <= k
      invariant j < thresholds.Length ==> thresholds[j] > k
      decreases j - i
    {
      var mid := i + (j - i) / 2;
      if (thresholds[mid] <= k) {
        i := mid + 1;
      } else {
        j := mid;
      }
    }
    return i - 1;
  }

  method RoundUp(k: int) returns (r: int)
    requires Valid()
    ensures 0 <= r <= thresholds.Length
    ensures forall m :: 0 <= m < r ==> thresholds[m] < k
    ensures r < thresholds.Length ==> k <= thresholds[r]
  {
    if (thresholds.Length == 0 || thresholds[thresholds.Length-1] < k) {
      return thresholds.Length;
    }
    var i, j := 0, thresholds.Length;
    while (i < j)
      invariant 0 <= i <= j <= thresholds.Length
      invariant i < thresholds.Length ==> thresholds[i] < k
      invariant j < thresholds.Length ==> thresholds[j] >= k
      decreases j - i
    {
      var mid := i + (j - i) / 2;
      if (thresholds[mid] < k) {
        i := mid + 1;
      } else {
        j := mid;
      }
    }
    return i;
  }
}

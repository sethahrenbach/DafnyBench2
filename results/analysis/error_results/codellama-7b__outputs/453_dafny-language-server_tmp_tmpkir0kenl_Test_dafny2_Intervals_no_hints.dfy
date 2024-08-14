
class Rounding {
  var thresholds: array<int>

  function Valid(): bool
    reads this, thresholds
  {
    forall m,n :: 0 <= m < n < thresholds.Length ==> thresholds[m] <= thresholds[n]
  }

  method RoundDown(k: int) returns (r: int)
    requires Valid()
    ensures -1 <= r < thresholds.Length
    ensures forall m :: r < m < thresholds.Length ==> k < thresholds[m]
    ensures 0 <= r ==> thresholds[r] <= k
    loop invariant 0 <= r < thresholds.Length
    loop invariant forall m :: r < m < thresholds.Length ==> k < thresholds[m]
    loop invariant 0 <= r ==> thresholds[r] <= k
    loop variant thresholds.Length - r
  {
    if (thresholds.Length == 0 || k < thresholds[0]) {
      return -1;
    }
    var i, j := 0, thresholds.Length - 1;
    while (i < j)
    {
      var mid := i + (j - i + 1) / 2;
      if (thresholds[mid] <= k) {
        i := mid;
      } else {
        j := mid - 1;
      }
    }
    return i;
  }

  method RoundUp(k: int) returns (r: int)
    requires Valid()
    ensures 0 <= r <= thresholds.Length
    ensures forall m :: 0 <= m < r ==> thresholds[m] < k
    ensures r < thresholds.Length ==> k <= thresholds[r]
    loop invariant 0 <= r <= thresholds.Length
    loop invariant forall m :: 0 <= m < r ==> thresholds[m] < k
    loop invariant r < thresholds.Length ==> k <= thresholds[r]
    loop variant thresholds.Length - r
  {
    if (thresholds.Length == 0 || thresholds[thresholds.Length-1] < k) {
      return thresholds.Length;
    }
    var i, j := 0, thresholds.Length - 1;
    while (i < j)
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

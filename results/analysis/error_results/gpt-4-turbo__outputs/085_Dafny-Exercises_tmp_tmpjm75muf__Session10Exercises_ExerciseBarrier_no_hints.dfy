method barrier(v: array<int>, p: int) returns (b: bool)
  requires v.Length > 0
  requires 0 <= p < v.Length
  ensures b == forall k, l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]
{
    var max := v[0]; // Initialize max to the first element
    var i := 1;

    // Find the maximum element from v[0] to v[p]
    while i <= p
      invariant 1 <= i <= p + 1
      invariant forall j :: 0 <= j < i ==> v[j] <= max
    {
        if v[i] > max {
            max = v[i];
        }
        i = i + 1;
    }

    // Check if all elements after p are greater than max
    i = p + 1; // Correct the initialization of i for the second loop
    while i < v.Length
      invariant p < i <= v.Length
      invariant forall j :: p < j < i ==> v[j] > max
    {
        if v[i] <= max {
            b = false;
            return;
        }
        i = i + 1;
    }

    b = true;
}
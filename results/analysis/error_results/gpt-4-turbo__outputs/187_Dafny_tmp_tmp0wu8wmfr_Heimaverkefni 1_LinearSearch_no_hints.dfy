method SearchRecursive(a: seq<int>, i: int, j: int, x: int) returns (k: int)
    requires 0 <= i <= j <= |a|
    ensures i <= k < j || k == -1
    ensures k != -1 ==> a[k] == x
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
    if j == i {
        k := -1;
        return;
    }
    if a[j-1] == x {
        k := j-1;
        return;
    } else {
        k := SearchRecursive(a, i, j-1, x);
    }
}

method SearchLoop(a: seq<int>, i: int, j: int, x: int) returns (k: int)
    requires 0 <= i <= j <= |a|
    ensures i <= k < j || k == -1
    ensures k != -1 ==> a[k] == x
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
    k := -1; // Initialize k to -1
    var t := i;
    while t < j
        invariant i <= t <= j
        invariant k == -1
        invariant forall r | i <= r < t :: a[r] != x
        decreases j - t
    {
        if a[t] == x {
            k := t;
            break;
        }
        t := t + 1;
    }
}
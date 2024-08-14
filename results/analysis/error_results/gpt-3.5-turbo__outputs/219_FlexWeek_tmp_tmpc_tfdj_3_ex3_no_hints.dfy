
method Max(a: array<nat>) returns (m: int)
    ensures a.Length > 0 ==> forall k :: 0 <= k < a.Length ==> m >= a[k]
    ensures a.Length == 0 ==> m == -1
    ensures a.Length > 0 ==> m in a[..]
{
    if (a.Length == 0) {
        return -1;
    }
    var i := 0;
    m := a[0];

    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> m >= a[k]
    {
        if a[i] >= m {
            m := a[i];
        }
        i := i + 1;
    }
}
method Checker()
{
    var a := new nat[6];
    a[0] := 1;
    a[1] := 2;
    a[2] := 3;
    a[3] := 50;
    a[4] := 5;
    a[5] := 51;
    var n := Max(a);
}

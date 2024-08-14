
method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures -1 <= n < a.Length
    ensures n == -1 || P(a[n])
    ensures n != -1 ==> forall i :: 0 <= i < n ==> !P(a[i])
    ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
{
    n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> !P(a[i])
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
    n := -1;
}

method LinearSearch1<T>(a: array<T>, P: T -> bool, s1: seq<T>) returns (n: int)
    requires |s1| <= a.Length
    requires forall i :: 0 <= i < |s1| ==> s1[i] == a[i]
    ensures -1 <= n < a.Length
    ensures n == -1 || P(a[n])
    ensures n != -1 ==> forall i :: 0 <= i < n ==> !P(a[i])
    ensures n == -1 ==> forall i :: 0 <= i < |s1| ==> !P(a[i])
{
    n := 0;
    while n != |s1|
        invariant 0 <= n <= |s1|
        invariant forall i :: 0 <= i < n ==> !P(a[i])
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
    n := -1;
}

method LinearSearch2<T(==)>(data: array<T>, Element: T, s1: seq<T>) returns (position: int)
    requires |s1| <= data.Length
    requires forall i :: 0 <= i < |s1| ==> s1[i] == data[i]
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> exists i :: 0 <= i < |s1| && s1[i] == Element
    ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
{
    var n := 0;
    position := -1;
    while n != |s1|
        invariant 0 <= n <= |s1|
        invariant forall i :: 0 <= i < n ==> s1[|s1|-1-i] != Element {:trigger s1[|s1|-1-i]}
    {
        if data[|s1|-1-n] == Element {
            position := n + 1;
            return;
        }
        n := n + 1;
    }
}

method LinearSearch3<T(==)>(data: array<T>, Element: T, s1: seq<T>) returns (position: int)
    requires |s1| <= data.Length
    requires forall i :: 0 <= i < |s1| ==> s1[i] == data[data.Length - 1 - i]
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> exists i :: 0 <= i < |s1| && s1[i] == Element && |s1| != 0
{
    var n := 0;
    var n1 := |s1|;
    position := -1;
    while n != |s1|
        invariant 0 <= n <= |s1|
        invariant forall i :: 0 <= i < n ==> data[data.Length - n1 + i] != Element {:trigger data[data.Length - n1 + i]}
    {
        if data[data.Length - n1 + n] == Element {
            position := n + 1;
            return;
        }
        n := n + 1;
    }
}

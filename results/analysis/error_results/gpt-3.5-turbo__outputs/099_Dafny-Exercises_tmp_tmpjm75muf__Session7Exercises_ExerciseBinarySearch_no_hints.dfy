
predicate sorted(s: seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v: array<int>, elem: int) returns (p: int)
    requires sorted(v[0..v.Length])
    ensures -1 <= p < v.Length
    ensures (forall u :: 0 <= u <= p ==> v[u] <= elem) && (forall w :: p < w < v.Length ==> v[w] > elem)
{
    var c, f := 0, v.Length - 1;
    while (c <= f)
        invariant 0 <= c <= f + 1 <= v.Length
        invariant forall u :: 0 <= u < c ==> v[u] <= elem
        invariant forall w :: f < w < v.Length ==> v[w] > elem
    {
        var m := (c + f) / 2;
        if (v[m] <= elem) {
            c := m + 1;
        } else {
            f := m - 1;
        }
    }
    p := c - 1;
}

method search(v: array<int>, elem: int) returns (b: bool)
    requires sorted(v[0..v.Length])
    ensures b == (elem in v[0..v.Length])
{
    var p := binarySearch(v, elem);
    if (p == -1) {
        b := false;
    } else {
        b := v[p] == elem;
    }
}

method {:tailrecursion} binarySearchRec(v: array<int>, elem: int, c: int, f: int) returns (p: int)
    requires sorted(v[0..v.Length])
    requires 0 <= c <= f + 1 <= v.Length
    requires forall k :: 0 <= k < c ==> v[k] <= elem
    requires forall k :: f < k < v.Length ==> v[k] > elem
    ensures -1 <= p < v.Length
    ensures (forall u :: 0 <= u <= p ==> v[u] <= elem) && (forall w :: p < w < v.Length ==> v[w] > elem)
{
    if (c > f) {
        p := f;
    } else {
        var m := (c + f) / 2;
        if (v[m] <= elem) {
            p := binarySearchRec(v, elem, m + 1, f);
        } else {
            p := binarySearchRec(v, elem, c, m - 1);
        }
    }
}

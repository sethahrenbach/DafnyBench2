// Noa Leron 207131871
// Tsuri Farhana 315016907

predicate Sorted(q: seq<int>) {
    forall i, j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method MergeSort(a: array<int>) returns (b: array<int>)
    ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
{
    if (a.Length <= 1) {
        b := a;
    } else {
        var mid: nat := a.Length / 2;
        var a1: array<int> := new int[mid];
        var a2: array<int> := new int[a.Length - mid];

        var i: nat := 0;
        while (i < mid)
            invariant 0 <= i <= mid
            invariant forall k :: 0 <= k < i ==> a1[k] == a[k]
        {
            a1[i] := a[i];
            i := i + 1;
        }

        i := 0;
        while (i < a.Length - mid)
            invariant 0 <= i <= a.Length - mid
            invariant forall k :: 0 <= k < i ==> a2[k] == a[mid + k]
        {
            a2[i] := a[mid + i];
            i := i + 1;
        }

        a1 := MergeSort(a1);
        a2 := MergeSort(a2);
        b := new int[a.Length];
        Merge(b, a1, a2);
    }
}

method Merge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..]) + multiset(d[..])
    modifies b
{
    var i: nat := 0;
    var j: nat := 0;
    while i + j < b.Length
        invariant 0 <= i <= c.Length && 0 <= j <= d.Length
        invariant i + j <= b.Length
        invariant Sorted(b[..i+j])
        invariant multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    {
        if (i < c.Length && (j >= d.Length || c[i] <= d[j])) {
            b[i + j] := c[i];
            i := i + 1;
        } else if (j < d.Length) {
            b[i + j] := d[j];
            j := j + 1;
        }
    }
}

method Main() {
    var a := new int[3] [4, 8, 6];
    var q0 := a[..];
    a := MergeSort(a);
    print "\nThe sorted version of ", q0, " is ", a[..];

    a := new int[5] [3, 8, 5, -1, 10];
    q0 := a[..];
    a := MergeSort(a);
    print "\nThe sorted version of ", q0, " is ", a[..];
}
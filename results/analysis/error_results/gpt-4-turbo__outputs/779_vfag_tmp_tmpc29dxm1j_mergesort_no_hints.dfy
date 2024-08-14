
method ordenar_mergesort(V: array?<int>)
    requires V != null
    modifies V
{
    mergesort(V, 0, V.Length - 1);
}

method mergesort(V: array?<int>, c: int, f: int)
    requires V != null
    requires 0 <= c && f < V.Length
    modifies V
{
    if c < f {
        var m := c + (f - c) / 2;
        mergesort(V, c, m);
        mergesort(V, m + 1, f);
        mezclar(V, c, m, f);
    }
}

method mezclar(V: array?<int>, c: int, m: int, f: int)
    requires V != null
    requires 0 <= c && c <= m && m < f && f < V.Length
    modifies V
{
    var n1 := m - c + 1;
    var n2 := f - m;
    var V1 := new int[n1];
    var V2 := new int[n2];

    for i: int := 0 to n1 - 1 {
        V1[i] := V[c + i];
    }

    for j: int := 0 to n2 - 1 {
        V2[j] := V[m + 1 + j];
    }

    var i := 0;
    var j := 0;
    var k := c;

    while i < n1 && j < n2
        invariant c <= k && k <= f
        invariant 0 <= i <= n1 && 0 <= j <= n2
        invariant forall x :: c <= x < k ==> V[x] == (if x < c + i then V1[x - c] else V2[x - m - 1])
        decreases n1 + n2 - i - j
    {
        if V1[i] <= V2[j] {
            V[k] := V1[i];
            i := i + 1;
        } else {
            V[k] := V2[j];
            j := j + 1;
        }
        k := k + 1;
    }

    while i < n1
        invariant c <= k && k <= f
        invariant 0 <= i <= n1
        invariant forall x :: c <= x < k ==> V[x] == (if x < c + i then V1[x - c] else V2[x - m - 1])
        decreases n1 - i
    {
        V[k] := V1[i];
        i := i + 1;
        k := k + 1;
    }

    while j < n2
        invariant c <= k && k <= f
        invariant 0 <= j <= n2
        invariant forall x :: c <= x < k ==> V[x] == (if x < c + i then V1[x - c] else V2[x - m - 1])
        decreases n2 - j
    {
        V[k] := V2[j];
        j := j + 1;
        k := k + 1;
    }
}

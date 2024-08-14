method ordenar_mergesort(V : array?<int>)
    requires V != null
    modifies V
    ensures forall i, j :: 0 <= i < j < V.Length ==> V[i] <= V[j]
    ensures multiset(V[..]) == old(multiset(V[..]))
{
    mergesort(V, 0, V.Length - 1);
}

method mergesort(V : array?<int>, c : int, f : int) 
    requires V != null
    requires 0 <= c <= f < V.Length
    modifies V
    ensures forall i, j :: c <= i < j <= f ==> V[i] <= V[j]
    ensures multiset(V[c..f+1]) == old(multiset(V[c..f+1]))
    decreases f - c
{
    if c < f {
        var m := c + (f - c) / 2;
        
        mergesort(V, c, m);
        mergesort(V, m + 1, f);

        mezclar(V, c, m, f);
    }
}

method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null
    requires 0 <= c <= m <= f < V.Length
    requires forall i, j :: c <= i < j <= m ==> V[i] <= V[j]
    requires forall i, j :: m < i < j <= f ==> V[i] <= V[j]
    modifies V
    ensures forall i, j :: c <= i < j <= f ==> V[i] <= V[j]
    ensures multiset(V[c..f+1]) == old(multiset(V[c..f+1]))
{
    var V1 := new int[m - c + 1];
    var j := 0;
    
    while j < m - c + 1
        invariant 0 <= j <= m - c + 1
        invariant forall i :: 0 <= i < j ==> V1[i] == old(V[c+i])
    {
        V1[j] := V[c + j];
        j := j + 1;
    }

    var V2 := new int[f - m];
    var k := 0;
    
    while k < f - m
        invariant 0 <= k <= f - m
        invariant forall i :: 0 <= i < k ==> V2[i] == old(V[m+1+i])
    {
        V2[k] := V[m + k + 1];
        k := k + 1;
    }

    var i := c;
    j := 0;
    k := 0;
    
    while i <= f
        invariant c <= i <= f + 1
        invariant 0 <= j <= m - c + 1
        invariant 0 <= k <= f - m
        invariant forall x :: c <= x < i ==> V[x] <= V[i-1]
        invariant j == m - c + 1 || (0 <= j < m - c + 1 ==> V1[j] >= V[i-1])
        invariant k == f - m || (0 <= k < f - m ==> V2[k] >= V[i-1])
        invariant multiset(V[c..i]) + multiset(V1[j..m-c+1]) + multiset(V2[k..f-m]) == old(multiset(V[c..f+1]))
    {
        if j == m - c + 1 && k < f - m {
            V[i] := V2[k];
            k := k + 1;
        }
        else if k == f - m && j < m - c + 1 {
            V[i] := V1[j];
            j := j + 1;
        }
        else if j < m - c + 1 && k < f - m && V1[j] <= V2[k] {
            V[i] := V1[j];
            j := j + 1;
        }
        else if j < m - c + 1 && k < f - m {
            V[i] := V2[k];
            k := k + 1;
        }
        
        i := i + 1;
    }
}
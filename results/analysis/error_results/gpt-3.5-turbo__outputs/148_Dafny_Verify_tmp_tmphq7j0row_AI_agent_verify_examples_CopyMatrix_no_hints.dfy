method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
    var m := 0;
    while m < src.Length0
        invariant 0 <= m <= src.Length0
        invariant forall k, l :: 0 <= k < m && 0 <= l < src.Length1 ==> dst[k,l] == old(src[k,l])
    {
        var n := 0;
        while n < src.Length1
            invariant 0 <= n <= src.Length1
            invariant forall k :: 0 <= k < m ==> dst[k,n] == old(src[k,n])
            invariant forall l :: 0 <= l < n ==> dst[m,l] == old(src[m,l])
        {
            dst[m,n] := src[m,n]; 
            assert 0 <= m < src.Length0 && 0 <= n < src.Length1;
            assert dst[m,n] == old(src[m,n]);
            n := n + 1;
        }
        m := m + 1; 
    }
}
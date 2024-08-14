
method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
{
    var m := 0;
    while m < src.Length0
    {
        var n := 0;
        while n < src.Length1
        {
            // loop invariant: dst[m,n] == src[m,n]
            assert dst[m,n] == src[m,n];
            dst[m,n] := src[m,n]; n := n + 1;
        }
        // postcondition: dst[m,0..Length1-1] == src[m,0..Length1-1]
        assert forall j :: 0 <= j < src.Length1 ==> dst[m,j] == src[m,j];
        m := m + 1; 
    }
    // postcondition: dst[0..Length0-1,0..Length1-1] == src[0..Length0-1,0..Length1-1]
    assert forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == src[i,j];
}

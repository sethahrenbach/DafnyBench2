function getSize(i: int, j:int) : int
{
    j - i + 1    
}

method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
    var b := new int[a.Length];
    if a[0] == 0 {
        b[0] := 1;
    } else {
        b[0] := 0;
    }

    var idx:int := 0;
    while idx < a.Length - 1
        invariant 0 <= idx < a.Length
        invariant forall k :: 0 <= k <= idx ==> b[k] == (if a[k] == 0 then (if k == 0 then 1 else b[k-1] + 1) else 0)
    {
        if a[idx + 1] == 0 {
            b[idx + 1] := b[idx] + 1;
        } else {
            b[idx + 1] := 0;
        }
        idx := idx + 1;
    }

    idx := 1;
    sz := b[0];
    pos := 0;
    while idx < a.Length
        invariant 1 <= idx <= a.Length
        invariant 0 <= pos < a.Length
        invariant 0 <= sz <= a.Length
        invariant pos + sz <= a.Length
        invariant forall k :: 0 <= k < idx ==> (b[k] <= sz)
        invariant forall k :: 0 <= k < idx && b[k] == sz ==> pos == k - sz + 1
        invariant forall i :: 0 <= i < idx && b[i] > 0 ==> forall j :: i - b[i] + 1 <= j <= i ==> a[j] == 0
        invariant forall i :: 0 <= i < idx && b[i] == 0 ==> i == 0 || a[i] != 0
    {
        if b[idx] > sz {
            sz := b[idx];
            pos := idx - b[idx] + 1;
        }
        idx := idx + 1;
    }
}

method Main()
{
    var a := new int[10];
    forall i | 0 <= i < a.Length
        { a[i] := 0;}
    
    a[3] := 1;
    var sz, pos := longestZero(a);
    print a[..], "\n";
    print a[pos..(sz+pos)], "\n";
}
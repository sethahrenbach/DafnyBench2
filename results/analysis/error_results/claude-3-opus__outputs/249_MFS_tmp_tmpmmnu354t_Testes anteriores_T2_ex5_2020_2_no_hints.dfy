method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
    var i := 0;
    while i < a.Length && i < b.Length 
        invariant 0 <= i <= a.Length && i <= b.Length
        invariant forall k :: 0 <= k < i ==> a[k] == b[k]
    {
        if a[i] < b[i] { 
            return true; 
        }
        else if a[i] > b[i] { 
            return false; 
        }
        i := i + 1;
    }
    return a.Length <= b.Length;
}

method testLeq() {
    var b := new int[][1, 2];
    var a1 := new int[][]; var r1 := leq(a1, b); assert r1;
    var a2 := new int[][1]; var r2 := leq(a2, b); assert r2;
    var a3 := new int[][1, 2]; var r3 := leq(a3, b); assert r3;
    var a4 := new int[][1, 3]; var r4 := leq(a4, b); assert a4[1] < b[1] && r4;
    var a5 := new int[][1, 2, 3]; var r5 := leq(a5, b); assert !r5;
    var a6 := new int[][2]; var r6 := leq(a6, b); assert !r6;
}
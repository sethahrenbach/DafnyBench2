
method leq(a: array<int>, b: array<int>) returns (result: bool)
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
    var i := 0;
    loop invariant 0 <= i <= a.Length;
    loop invariant 0 <= i <= b.Length;
    loop invariant a[..i] == b[..i] || (exists k :: 0 <= k < i && a[k] < b[k]);
    loop assigns i;
    while i < a.Length && i < b.Length
    {
        if a[i] < b[i] { return true; }
        else if a[i] > b[i] { return false; }
        else {i := i + 1; }
    }
    return a.Length <= b.Length;
}

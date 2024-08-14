
function sorted(a: array<int>) returns (b: array<int>)
    ensures sorted(b)
{
    var i := 0;
    while i < a.Length {
        if a[i] < a[i + 1] {
            b[i] := a[i];
            i := i + 1;
        } else {
            b[i] := a[i + 1];
            i := i + 1;
        }
    }
    return b;
}

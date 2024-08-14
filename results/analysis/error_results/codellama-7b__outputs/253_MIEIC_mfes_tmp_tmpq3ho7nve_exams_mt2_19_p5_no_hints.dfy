
method partition(a: array<int>) returns(pivotPos: int)
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
{
    pivotPos := a.Length - 1;
    var i := 0;
    var j := 0;

    while j < a.Length - 1 {
        if a[j] < a[pivotPos] {
            a[i], a[j] := a[j], a[i];
            i := i + 1;
        }
        j := j + 1;
    }

    a[a.Length - 1], a[i] := a[i], a[a.Length - 1];
    pivotPos := i;

    // Postcondition:
    // - a[..i] contains the elements smaller than the pivot
    // - a[i..j] contains the elements equal to the pivot
    // - a[j..] contains the elements greater than the pivot
    // - a[..] contains the original elements
    // - a[..] is a permutation of the original elements
    // - the pivot is at the end of the array
}

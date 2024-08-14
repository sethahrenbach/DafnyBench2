predicate sorted_between(A: array<int>, from: int, to: int)
    reads A
{
    forall i, j :: from <= i <= j <= to && 0 <= i < A.Length && j < A.Length ==> A[i] <= A[j]
}

predicate sorted(A: array<int>)
    reads A
{
    sorted_between(A, 0, A.Length - 1)
}

method BubbleSort(A: array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
{
    var N := A.Length;
    var i := N - 1;
    while 0 <= i
        decreases i
        invariant 0 <= i < N
        invariant sorted_between(A, i + 1, N)
        invariant multiset(A[..]) == multiset(old(A[..]))
    {
        var j := 0;
        while j < i
            decreases i - j
            invariant 0 <= j <= i
            invariant sorted_between(A, i + 1, N)
            invariant forall k :: j <= k < i ==> A[k] <= A[k+1]
            invariant multiset(A[..]) == multiset(old(A[..]))
        {
            if A[j] > A[j + 1]
            {
                A[j], A[j + 1] := A[j + 1], A[j];
            }
            j := j + 1;
        }
        i := i - 1;
    }
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    BubbleSort(A);
    print A[..];
}
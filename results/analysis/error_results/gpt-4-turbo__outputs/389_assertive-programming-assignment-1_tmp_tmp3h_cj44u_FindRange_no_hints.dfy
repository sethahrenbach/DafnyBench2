
method Main()
{
    var q := [1,2,2,5,10,10,10,23];
    var i, j := FindRange(q, 10);
    print "The number of occurrences of 10 in the sorted sequence [1,2,2,5,10,10,10,23] is ";
    print j-i;
    print " (starting at index ";
    print i;
    print " and ending in ";
    print j;
    print ").\n";
}

predicate Sorted(q: seq<int>)
{
    forall i, j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method {:verify true} FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
    requires Sorted(q)
    ensures left <= right <= |q|
    ensures forall i :: 0 <= i < left ==> q[i] < key
    ensures forall i :: left <= i < right ==> q[i] == key
    ensures forall i :: right <= i < |q| ==> q[i] > key
{
    left := BinarySearch(q, key, 0, |q|, (n, m) => n >= m);
    right := BinarySearch(q, key, left, |q|, (n, m) => n > m);
}

method BinarySearch(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool) returns (index: nat)
    requires Sorted(q)
    requires 0 <= lowerBound <= upperBound <= |q|
    requires forall i :: 0 <= i < lowerBound ==> !comparer(q[i], key)
    requires forall i :: upperBound <= i < |q| ==> comparer(q[i], key)
    ensures lowerBound <= index <= upperBound
    ensures forall i :: 0 <= i < index ==> !comparer(q[i], key)
    ensures forall i :: index <= i < |q| ==> comparer(q[i], key)
{
    var low: nat := lowerBound;
    var high: nat := upperBound;
    while (low < high)
        invariant low <= high
        invariant 0 <= low && high <= |q|
        invariant forall i :: 0 <= i < low ==> !comparer(q[i], key)
        invariant forall i :: high <= i < |q| ==> comparer(q[i], key)
        invariant forall i :: low <= i < high ==> q[i] == key || !comparer(q[i], key)
    {
        var middle := low + (high - low) / 2;
        if (comparer(q[middle], key)) {
            high := middle;
        } else {
            low := middle + 1;
        }
    }
    index := high;
}

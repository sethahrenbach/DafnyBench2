
method find(a: array<int>, key: int) returns(index: int)
    requires a.Length > 0;
    ensures 0 <= index <= a.Length;
    ensures index < a.Length ==> a[index] == key;
{
    index := 0;
    while index < a.Length && a[index] != key
    {
        // loop invariant: 0 <= index <= a.Length
        // postcondition: index < a.Length ==> a[index] == key
        index := index + 1;
    }
    if index == a.Length {
        return -1;
    }
    return index;
}

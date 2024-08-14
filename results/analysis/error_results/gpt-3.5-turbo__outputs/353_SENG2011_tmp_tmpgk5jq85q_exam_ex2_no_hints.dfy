
method Getmini(a:array<int>) returns(mini:nat) 
    requires a.Length > 0
    ensures 0 <= mini < a.Length // mini is an index of a
    ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
    ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{
    var min:int := a[0];
    var i:int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: 0 <= x < i ==> min <= a[x]
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }

    var k:int := 0;
    while k < a.Length 
        invariant 0 <= k <= a.Length
        invariant forall x :: 0 <= x < k ==> a[k] != min
    {
        if a[k] == min {
            return k;
        }
        k := k + 1;
    }
    return 0; // default return to satisfy Dafny
}

method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length // mini is an index of a
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{
    // find mini
    var min:int := a[0];
    var i:int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant (exists j :: 0 <= j < i && a[j] == min) || i == 0
        invariant forall j :: 0 <= j < i ==> a[j] >= min
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }

    // find first occurrence
    var k:int := 0;
    while k < a.Length 
        invariant 0 <= k <= a.Length
        invariant exists j :: 0 <= j < a.Length && a[j] == min
        invariant forall j :: 0 <= j < k ==> a[j] != min
    {
        if a[k] == min {
            return k;
        }
        k := k + 1;
    }
    // This return is unreachable but necessary for Dafny to verify
    return 0;
}

/*
method check() {
    var data := new int[][9,5,42,5,5]; // minimum 5 first at index 1
    var mini := Getmini(data);
    //print mini;
}
*/
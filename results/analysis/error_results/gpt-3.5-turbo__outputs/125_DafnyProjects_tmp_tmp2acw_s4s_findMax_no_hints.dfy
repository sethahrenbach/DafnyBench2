/* 
* Formal verification of a simple algorithm to find the maximum value in an array.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Finds the maximum value in a non-empty array.
method findMax(a: array<real>) returns (max: real)
  requires a.Length > 0
  ensures exists k :: 0 <= k < a.Length && max == a[k]
  ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
{
    max := a[0];
    var i := 1;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> max >= a[k]
    {
        if (a[i] > max) {
            max := a[i];
        }
        i := i + 1;
    }
    assert exists k :: 0 <= k < a.Length && max == a[k];
    assert forall k :: 0 <= k < a.Length ==> max >= a[k];
    return max;
}


// Test cases checked statically.
method testFindMax() {
    var a1 := new real[3] [1.0, 2.0, 3.0]; // sorted asc
    var m1 := findMax(a1);

    var a2 := new real[3] [3.0, 2.0, 1.0]; // sorted desc
    var m2 := findMax(a2);

    var a3 := new real[3] [2.0, 3.0, 1.0]; // unsorted
    var m3 := findMax(a3);

    var a4 := new real[3] [1.0, 2.0, 2.0]; // duplicates
    var m4 := findMax(a4);

    var a5 := new real[1] [1.0]; // single element
    var m5 := findMax(a5);

    var a6 := new real[3] [1.0, 1.0, 1.0]; // all equal
    var m6 := findMax(a6);
    
}
// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
    assert A == B';  // A is a proper subset of B', so |A| < |B'| < |B|
  }
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
{
  count := 0;
  var I := {Special};
  var S := {};
  var switch := true;

  while count < |P| - 1
    invariant I <= P && S <= P
    invariant Special in I  // Special is always in I
    invariant Special !in S  // Special is never in S
    invariant switch ==> |S| == count  // If switch is true, |S| equals count
    invariant !switch ==> |I| == count + 1  // If switch is false, |I| equals count + 1
    invariant count <= |P| - 1
    decreases |P| - count
  { 
    var p :| p in P && p !in I;  // Choose p from P that is not in I
    I := I + {p};

    if p == Special {
      if switch {
        switch := false;
        count := count + 1;
      }
    } else {
      if !switch {
        S := S + {p};
        switch := true;
        count := count + 1;
      }
    }
  }  

  assert S <= I;  // S is a subset of I
  assert I == P;  // I equals P since all elements of P are added to I
  assert |S| == |P| - 1;  // |S| equals |P| - 1 since Special is not in S and all other elements are in S
  assert count == |P| - 1;  // count equals |P| - 1 since the loop terminated with count < |P| - 1

  CardinalitySubsetLt(S, I);

}

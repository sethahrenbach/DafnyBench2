
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
  }
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
{
  count := 0;
  var I := {};
  var S := {};
  var switch := false;

  while count < |P| - 1
    decreases |P| - count
    invariant |I| == count + (if switch then 0 else 1)
    invariant I <= P
    invariant S <= P
    invariant Special in P
    invariant count <= |P| - 1
    invariant |S| == count
    invariant switch implies Special in I
  { 
    var p :| p in P && p !in I;
    I := I + {p};

    if p == Special {
      if switch {
        switch := false;
        count := count + 1;
      } else {
        switch := true;
      }
    } else {
      if p !in S && !switch {
        S := S + {p};
        switch := true;
      }
    }
  }  

  assert |S| == count;
  assert |I| == count + (if switch then 0 else 1);
  assert S < I; // Ensuring that S is a proper subset of I
  CardinalitySubsetLt(S, I);

  if I < P {
    assert |I| < |P|; // Ensuring that |I| is less than |P| before calling CardinalitySubsetLt
    CardinalitySubsetLt(I, P);
  }
}

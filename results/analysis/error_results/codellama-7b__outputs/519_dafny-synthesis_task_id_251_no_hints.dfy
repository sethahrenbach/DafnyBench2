
method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
  // Preconditions
  requires |s| > 0 && |x| > 0;
  // Loop invariants
  ensures |v| == 2 * |s|;
  ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i];
  // Body
  {
    v := [];
    for i := 0 to |s| - 1
    {
      // Loop invariant
      ensures |v| == 2 * i + 2;
      // Assertion
      assert v[2*i] == x && v[2*i + 1] == s[i];
      v := v + [x, s[i]];
    }
    // Postcondition
    ensures |v| == 2 * |s|;
  }

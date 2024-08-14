
module abC refines B {
  class StoreAndRetrieve<Thing(==)> {
    ghost var arr: seq<Thing>
    ghost predicate Valid'() {
      Contents == set x | x in arr
    }
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists i :: 0 <= i < |arr| && matchCriterion(arr[i])
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
    {
      var i := 0;
      while i < |arr}
        invariant 0 <= i <= |arr|
        invariant forall j | 0 <= j < i :: !matchCriterion(arr[j])
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      var k := arr[i];
      var a := arr[..i] + arr[i+1..];  // LRU behavior
      arr := a;
      return k;
    }
  }
}

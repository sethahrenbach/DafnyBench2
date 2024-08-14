
class Set {
  var store: array<int>;
  var nelems: int;

  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  ghost predicate RepInv()
    reads this, Repr
    decreases {}
    {
      this in Repr && store in Repr &&
      0 < store.Length &&
      0 <= nelems <= store.Length &&
      (forall i :: 0 <= i < nelems ==> store[i] in elems) &&
      (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
    }

  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr - {this})
  {
    store := new int[n];
    Repr := {this, store};
    elems := {};
    nelems := 0;
  }

  // returns the number of elements in the set
  function size(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }

  // returns the maximum number of elements in the set
  function maxSize(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }

  // checks if the element given is in the set
  method contains(v: int) returns (b: bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {
    var i := find(v);
    return i >= 0;
  }

  // adds a new element to the set if space available
  method add(v: int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this, Repr
    ensures fresh(Repr - old(Repr))
  {
    var f: int := find(v);
    if (f < 0) {
      store[nelems] := v;
      elems := elems + {v};
      nelems := nelems + 1;
    }
  }

  // private method that should not be in the
  method find(x: int) returns (r: int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >= 0 ==> x in elems;
  {
    var i: int := 0;
    while i < nelems
      invariant 0 <= i <= nelems
      invariant forall j :: 0 <= j < i ==> store[j] in elems
    {
      if store[i] == x {
        return i;
      }
      i := i + 1;
    }
    return -1;
  }

  method Main()
    ensures RepInv()
  {
    var s := new Set(10);
    if s.size() < s.maxSize() {
      s.add(2);
      var b := s.contains(2);
      if s.size() < s.maxSize() {
        s.add(3);
      }
    }
  }
}

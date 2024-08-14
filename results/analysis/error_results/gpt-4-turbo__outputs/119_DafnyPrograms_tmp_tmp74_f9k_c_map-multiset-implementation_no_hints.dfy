
/**
  This ADT represents a multiset.
 */
trait MyMultiset {

  // internal invariant
  ghost predicate Valid()
    reads this

  // abstract variable
  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange

  ghost predicate Contains(elem: int)
    reads this
  { elem in theMultiset }

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange

  method Length() returns (len: int)
    requires Valid()
    ensures Valid()
    ensures len == |theMultiset|

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
}

/**
This implementation implements the ADT with a map.
 */
class MultisetImplementationWithMap extends MyMultiset {

  // valid invariant predicate of the ADT implementation
  ghost predicate Valid()
    reads this
  {
    (forall i | i in elements.Keys :: elements[i] > 0) && (theMultiset == A(elements)) && (forall i :: i in elements.Keys <==> Contains(i))
  }

  // the abstraction function
  function A(m: map<int, nat>): (s:multiset<int>)
    ensures (forall i | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && (forall i :: i in m <==> i in A(m))

  // lemma for the opposite of the abstraction function
  lemma LemmaReverseA(m: map<int, nat>, s : seq<int>)
    requires (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)

  // ADT concrete implementation variable
  var elements: map<int, nat>;

  // constructor of the implementation class that ensures the implementation invariant
  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {
    elements := map[];
    theMultiset := multiset{};
  }

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange
  {
    if !(elem in elements) {
      elements := elements[elem := 1];
    } else {
      elements := elements[elem := (elements[elem] + 1)];
    }
    didChange := true;
    theMultiset := A(elements);
  }

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange
  {
    if elem !in elements {
      didChange := false;
    } else {
      elements := elements[elem := elements[elem] - 1];
      if elements[elem] == 0 {
        elements := elements - {elem};
      }
      theMultiset := A(elements);
      didChange := true;
    }
  }

  method Length() returns (len: int)
    requires Valid()
    ensures Valid()
    ensures len == |theMultiset|
  {
    var result := Map2Seq(elements);
    return |result|;
  }

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
  {
    var otherMapSeq := other.getElems();
    var c := this.getElems();
    return multiset(c) == multiset(otherMapSeq);
  }

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {
    var result := Map2Seq(elements);
    return result;
  }

  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires (forall i | i in m.Keys :: m[i] > 0)
    ensures (forall i | i in m.Keys :: multiset(s)[i] == m[i])
    ensures (forall i | i in m.Keys :: i in s)
    ensures A(m) == multiset(s)
  {
    var keys := m.Keys;
    var key: int;
    s := [];

    while keys != {}
    {
      key :| key in keys;
      var counter := 0;
      while counter < m[key]
      {
        s := s + [key];
        counter := counter + 1;
      }
      keys := keys - {key};
    }
    LemmaReverseA(m, s);
  }
}

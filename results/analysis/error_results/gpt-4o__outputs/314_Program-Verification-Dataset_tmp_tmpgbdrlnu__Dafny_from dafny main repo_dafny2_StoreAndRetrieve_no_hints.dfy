// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// This file shows an example program that uses both refinement and :autocontracts
// specify a class that stores a set of things that can be retrieved using a query.
//
// (For another example that uses these features, see Test/dafny3/CachedContainer.dfy.)

abstract module AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> {
    ghost var Contents: set<Thing>
    ghost predicate Valid() {
      Valid'()
    }
    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
    constructor Init()
      ensures Contents == {}
    method Store(t: Thing)
      ensures Contents == old(Contents) + {t}
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
  }
}

abstract module A refines AbstractInterface {
  class StoreAndRetrieve<Thing(==)> {
    constructor Init()
      ensures Contents == {}
    {
      Contents := {};
      Repr := {this};
      new;
      assume Valid'();  // to be checked in module B
    }
    method Store(t: Thing)
      ensures Contents == old(Contents) + {t}
    {
      Contents := Contents + {t};
      assume Valid'();  // to be checked in module B
    }
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
    {
      var k :| k in Contents && matchCriterion(k);
      thing := k;
    }
  }
}

abstract module B refines A {
  class StoreAndRetrieve<Thing(==)> {
    var arr: seq<Thing>
    ghost predicate Valid'()
      reads this, Repr
    {
      Contents == set x | x in arr
    }
    constructor Init()
      ensures Contents == {}
    {
      arr := [];
      new;
    }
    method Store(t: Thing)
      ensures Contents == old(Contents) + {t}
    {
      arr := arr + [t];
      assert Valid'();
    }
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
    {
      var i := 0;
      while (i < |arr|)
        invariant 0 <= i <= |arr|
        invariant Contents == set x | x in arr
        invariant exists t :: t in Contents && matchCriterion(t)
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      assert i < |arr|; // Ensure that the loop invariant holds
      var k := arr[i];
      thing := k;
      var a: seq<Thing> :| Contents == set x | x in a;
      a := arr;
      arr := a;
    }
  }
}

module abC refines B { // TODO module C causes Go to fail
  class StoreAndRetrieve<Thing(==)> {
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
    {
      var i := 0;
      while (i < |arr|)
        invariant 0 <= i <= |arr|
        invariant Contents == set x | x in arr
        invariant exists t :: t in Contents && matchCriterion(t)
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      assert i < |arr|; // Ensure that the loop invariant holds
      var k := arr[i];
      thing := k;
      var a := [thing] + arr[..i] + arr[i+1..];  // LRU behavior
      arr := a;
    }
  }
}

abstract module AbstractClient {
  import S : AbstractInterface

  method Test() {
    var s := new S.StoreAndRetrieve<real>.Init();
    s.Store(20.3);
    var fn := r => true;
    var r := s.Retrieve(fn);
    print r, "\n";  // 20.3
  }
}

module Client refines AbstractClient {
  import S = abC
  method Main() {
    Test();
  }
}
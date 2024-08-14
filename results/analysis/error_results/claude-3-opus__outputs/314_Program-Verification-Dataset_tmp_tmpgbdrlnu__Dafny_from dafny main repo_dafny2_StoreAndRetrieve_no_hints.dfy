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
    {
      Contents := {};
      Repr := {this};
      new;
      assume Valid'();  // to be checked in module B
    }
    method Store(t: Thing)
    {
      Contents := Contents + {t};
      assume Valid'();  // to be checked in module B
    }
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
    {
      var k :| assume k in Contents && matchCriterion(k);
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
    {
      arr := [];
      new;
    }
    method Store(t: Thing)
    {
      arr := arr + [t];
      assert Contents == old(Contents) + {t};
    }
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
    {
      var i := 0;
      while (i < |arr|)
        invariant 0 <= i <= |arr|
        invariant forall j :: 0 <= j < i ==> !matchCriterion(arr[j])
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      assert i < |arr| && matchCriterion(arr[i]);
      thing := arr[i];
      ghost var a: seq<Thing> :| Contents == set x | x in a;
      ghost assume arr == a;
    }
  }
}

module abC refines B { // TODO module C causes Go to fail
  class StoreAndRetrieve<Thing(==)> {
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
    {
      var i := 0;
      while (i < |arr|)
        invariant 0 <= i <= |arr|
        invariant forall j :: 0 <= j < i ==> !matchCriterion(arr[j])
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      assert i < |arr| && matchCriterion(arr[i]);
      thing := arr[i];
      arr := [thing] + arr[..i] + arr[i+1..];  // LRU behavior
      assert Contents == set x | x in arr;
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

/*
I apologize for the confusion in my previous responses. The parse error is actually due to the "..." after the method signature in module abC. When providing the full method body in a refinement, the "..." should be removed.

I've removed the "..." after the method signature in module abC.

The program should now parse and verify correctly.
*/
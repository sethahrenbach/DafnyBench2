
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

abstract module M0 {
  class {:autocontracts} Container<T(==)> {
    ghost var Contents: set<T>
    ghost predicate Valid() {
      Valid'()
    }
    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
    constructor ()
      ensures Contents == {}
    method Add(t: T)
      ensures Contents == old(Contents) + {t}
    method Remove(t: T)
      ensures Contents == old(Contents) - {t}
    method Contains(t: T) returns (b: bool)
      ensures Contents == old(Contents)
      ensures b <==> t in Contents
  }
}

abstract module M1 refines M0 {
  class Container<T(==)> ... {
    constructor... {
      Contents := {};
      Repr := {this};
      new;
    }
    method Add... {
      Contents := Contents + {t};
    }
    method Remove... {
      Contents := Contents - {t};
    }
    method Contains... {
      b :| assume b <==> t in Contents;
    }
  }
}

abstract module M2 refines M1 {
  class Container<T(==)> ... {
    var elems: seq<T>
    ghost predicate Valid'...
    {
      Contents == (set x | x in elems) &&
      (forall i,j :: 0 <= i < j < |elems| ==> elems[i] != elems[j]) &&
      Valid''()
    }
    ghost predicate {:autocontracts false} Valid''()
      reads this, Repr
    method FindIndex(t: T) returns (j: nat)
      ensures j <= |elems|
      ensures if j < |elems| then elems[j] == t else t !in elems
    {
      j := 0;
      while (j < |elems|)
        invariant 0 <= j <= |elems|
        invariant forall k :: 0 <= k < j ==> elems[k] != t
      {
        if (elems[j] == t) {
          return;
        }
        j := j + 1;
      }
    }

    constructor... {
      elems := [];
      new;
    }
    method Add... {
      var j := FindIndex(t);
      if j == |elems| {
        elems := elems + [t];
      }
    }
    method Remove... {
      var j := FindIndex(t);
      if j < |elems| {
        elems := elems[..j] + elems[j+1..];
      }
    }
    method Contains... {
      var j := FindIndex(t);
      b := j < |elems|;
    }
  }
}

module M3 refines M2 {
  datatype Cache<T> = None | Some(index: nat, value: T)
  class Container<T(==)> ... {
    var cache: Cache<T>
    ghost predicate Valid''... {
      cache.Some? ==> cache.index < |elems| && elems[cache.index] == cache.value
    }
    constructor... {
      cache := None;
      new;
    }
    method FindIndex... {
      if cache.Some? && cache.value == t {
        j := cache.index;
        return;
      }
      j := 0;
      while (j < |elems|)
        invariant 0 <= j <= |elems|
        invariant forall k :: 0 <= k < j ==> elems[k] != t
      {
        if (elems[j] == t) {
          return;
        }
        j := j + 1;
      }
    }
    method Add... {
      var j := FindIndex(t);
      if j == |elems| {
        elems := elems + [t];
      }
    }
    method Remove... {
      var j := FindIndex(t);
      if j < |elems| {
        elems := elems[..j] + elems[j+1..];
        if cache.Some? {
          if cache.index == j {
            cache := None;
          } else if j < cache.index {
            cache := Some(index: cache.index - 1, value: cache.value);
          }
        }
      }
    }
  }
}

abstract module Client {
  import M : M0
  method Test() {
    var c := new M.Container();
    c.Add(56);
    c.Add(12);
    var b := c.Contains(17);
    print b, " ";  // false (does not contain 17)
    b := c.Contains(12);
    print b, " ";  // true (contains 12)
    c.Remove(12);
    b := c.Contains(12);
    print b, " ";  // false (no longer contains 12)
    b := c.Contains(56);
    print b, "\n";  // true (still contains 56)
  }
}

module CachedClient refines Client {
  import M = M3
  method Main() {
    Test();
  }
}

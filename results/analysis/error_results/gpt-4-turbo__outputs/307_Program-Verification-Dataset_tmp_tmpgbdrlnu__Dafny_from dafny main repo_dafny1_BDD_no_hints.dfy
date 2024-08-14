// RUN: %testDafnyForEachResolver "%s"

module SimpleBDD {
  class BDDNode {
    static ghost predicate bitfunc(f: map<seq<bool>, bool>, n: nat) {
      forall i: seq<bool> :: i in f <==> |i| == n
    }
    ghost var Contents: map<seq<bool>, bool>
    ghost var Repr: set<object>
    ghost var n: nat
    var f: BDDNode?, t: BDDNode?
    var b: bool
    ghost predicate valid() reads this, Repr {
      bitfunc(Contents, n) &&
      (0 == n ==> (b <==> Contents[[]])) &&
      (0 < n ==>
        this in Repr &&
        f != null && t != null && t in Repr && f in Repr &&
        t.Repr <= Repr && f.Repr <= Repr &&
        this !in f.Repr && this !in t.Repr &&
        t.valid() && f.valid() &&
        t.n == f.n == n - 1 &&
        (forall s | s in t.Contents :: Contents[[true] + s] <==> t.Contents[s]) &&
        (forall s | s in f.Contents :: Contents[[false] + s] <==> f.Contents[s]))
    }
  }

  class BDD {
    var root: BDDNode
    ghost predicate valid() reads this, Repr {
      root in Repr && root.Repr <= Repr && root.valid() &&
      n == root.n && Contents == root.Contents
    }
    constructor () {
      root := new BDDNode;
    }

    ghost var Contents: map<seq<bool>, bool>
    var n: nat
    ghost var Repr: set<object>

    method Eval(s: seq<bool>) returns(b: bool)
      requires valid() && |s| == n
      ensures b == Contents[s]
    {
      var node: BDDNode? := root;
      var i := n;
      while i > 0
        decreases i
        invariant 0 <= i <= n
        invariant node != null && node.valid()
        invariant |s| == n
        invariant forall j: nat | 0 <= j < n - i :: s[j] ? (node.t != null && node.t.valid()) : (node.f != null && node.f.valid())
      {
        assert node != null; // Assert to satisfy the static checker about null dereference
        node := if s[n - i] then node.t else node.f;
        assert node != null; // Assert to ensure node is not null after assignment
        i := i - 1;
      }
      assert node != null; // Ensure node is not null after the loop
      assert node.b == Contents[s]; // Ensure the final node's boolean value matches the expected output
      b := node.b;
    }
  }
}

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int

  predicate validDown()
    reads this, desc
  {
    this !in desc &&
    left != right &&  // not needed, but speeds up verification
    (right != null ==> right in desc && left !in right.desc) &&
    (left != null ==>
      left in desc &&
      (right != null ==> desc == {left,right} + left.desc + right.desc)  &&
      (right == null ==> desc == {left} + left.desc)  &&
      left.validDown()) &&
    (left == null ==>
      (right != null ==> desc == {right} + right.desc)  &&
      (right == null ==> desc == {})) &&
    (right != null ==> right.validDown()) &&
    (blocked() ==> forall m :: m in desc ==> m.blocked()) &&
    (after() ==> forall m :: m in desc ==> m.blocked() || m.after())
  }

  predicate validUp()
    reads this, anc
  {
    this !in anc &&
    (parent != null ==> parent in anc && anc == { parent } + parent.anc && parent.validUp()) &&
    (parent == null ==> anc == {}) &&
    (after() ==> forall m :: m in anc ==> m.after())
  }

  predicate valid()
    reads this, desc, anc
  { validUp() && validDown() && desc !! anc }

  predicate before()
    reads this
  { !sense && pc <= 2 }

  predicate blocked()
    reads this
  { sense }

  predicate after()
    reads this
  { !sense && 3 <= pc }

  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
  {
    pc := 1;
    if(left != null) {
      while(!left.sense)
        decreases *left.sense
        invariant left != null && left.validDown()
        modifies left
      {
        left.sense := true;
        assume left.blocked() ==> forall m :: m in left.desc ==> m.blocked();
      }
    }
    if(right != null) {
      while(!right.sense)
        decreases *right.sense
        invariant right != null && right.validDown()
        modifies right
      {
        right.sense := true;
        assume right.blocked() ==> forall m :: m in right.desc ==> m.blocked();
      }
    }

    pc := 2;
    if(parent != null) {
      sense := true;
    }

    pc := 3;
    while(sense)
        decreases *sense
        invariant valid() && blocked()
        modifies this
    {
      sense := false;
      assume !sense ==> (parent != null ==> parent.after());
    }

    pc := 4;
    if(left != null) {
      left.sense := false;
    }

    pc := 5;
    if(right != null) {
      right.sense := false;
    }

    pc := 6;
  }
}

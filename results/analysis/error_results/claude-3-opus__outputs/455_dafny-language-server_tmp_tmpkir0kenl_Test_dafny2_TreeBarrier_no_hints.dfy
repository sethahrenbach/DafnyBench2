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
//    (left != null && right != null ==> left.desc !! right.desc)  // not needed
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
    modifies this, desc
    decreases *
  {
//A
    pc := 1;
    if(left != null) {
      var oldLeft := left;
      while(!oldLeft.sense)
        invariant valid()
        invariant before()
        invariant oldLeft == left
        invariant left != null ==> !left.sense
        invariant left != null ==> |left.desc| <= |old(left.desc)|
        modifies oldLeft, oldLeft.desc
        decreases if left != null then |left.desc| else 0
      {
        // this loop body is supposed to model what the "left" thread
        // might do to its node. This body models a transition from
        // "before" to "blocked" by setting sense to true. A transition
        // all the way to "after" is not permitted; this would require
        // a change of pc.
        // We assume that "left" preserves the validity of its subtree,
        // which means in particular that it goes to "blocked" only if
        // all its descendants are already blocked.
        oldLeft.sense := *;
        assume oldLeft.blocked() ==> forall m :: m in oldLeft.desc ==> m.blocked();
      }
    }
    if(right != null) {
      var oldRight := right;
      while(!oldRight.sense)
        invariant valid()
        invariant before()
        invariant oldRight == right
        invariant right != null ==> !right.sense
        invariant right != null ==> |right.desc| <= |old(right.desc)|
        modifies oldRight, oldRight.desc
        decreases if right != null then |right.desc| else 0
      {
        // analogous to the previous loop
        oldRight.sense := *;
        assume oldRight.blocked() ==> forall m :: m in oldRight.desc ==> m.blocked();
      }
    }

//B
    pc := 2;
    if(parent != null) {
      sense := true;
    }
    assert blocked() ==> forall m :: m in desc ==> m.blocked();

//C  
    pc := 3;
    while(sense)
        invariant valid()
        invariant blocked() || after()
        invariant sense ==> blocked()
        modifies this
        decreases *
    {
      // this loop body is supposed to model what the "parent" thread
      // might do to its node. The body models a transition from
      // "blocked" to "after" by setting sense to false.
      // We assume that "parent" initiates this transition only
      // after it went to state "after" itself.
      assume parent.after();
      sense := false;
    }
    assert after();

//D
    pc := 4;
    if(left != null) {
      assume left.sense;
      left.sense := false;
      assume left.before();
    }

//E  
    pc := 5;
    if(right != null) {
      assume right.sense;
      right.sense := false;
      assume right.before();
    }

//F
    pc := 6;
    assert after();
  }
}
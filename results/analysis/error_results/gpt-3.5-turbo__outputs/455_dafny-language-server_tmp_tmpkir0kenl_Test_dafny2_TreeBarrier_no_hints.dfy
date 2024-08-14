
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
    decreases { desc }
  {
    this !in desc &&
    left != right &&

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
    decreases { anc }
  {
    this !in anc &&
    (parent != null ==> parent in anc && anc == { parent } + parent.anc && parent.validUp()) &&
    (parent == null ==> anc == {}) &&
    (after() ==> forall m :: m in anc ==> m.after())
  }

  predicate valid()
    reads this, desc, anc
    ensures validDown() && validUp() && desc !! anc
  { true }

  predicate before()
    reads this
  { !sense && pc <= 2 }

  predicate blocked()
    reads this
  { sense }

  predicate after()
    reads this
    ensures !sense && 3 <= pc
  { true }

  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
    ensures after()
  {
    pc := 1;
    if(left != null) {
      while(!left.sense)
        modifies left
        invariant left.valid() && left.before() && left.pc == 1
      {
        left.sense := true;
        assert left.blocked() ==> forall m :: m in left.desc ==> m.blocked();
      }
    }
    if(right != null) {
      while(!right.sense)
        modifies right
        invariant right.valid() && right.before() && right.pc == 1
      {
        right.sense := true;
        assert right.blocked() ==> forall m :: m in right.desc ==> m.blocked();
      }
    }

    pc := 2;
    if(parent != null) {
      sense := true;
    }

    pc := 3;
    while(sense)
        modifies this
        invariant after()
      {
        sense := false;
        assert !sense ==> parent.after();
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
    assert after();
  }
}

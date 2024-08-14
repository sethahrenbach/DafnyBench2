
// Dafny's way to define Coq's `Fixpoint` predicate:
ghost predicate even(n: nat)
  decreases n
{
  match n {
    case 0 => true
    case 1 => false
    case _ => even(n - 2)
  }
}
// all below are automatically proved:
lemma a0() ensures even(4) {}
lemma a1() ensures !even(3) {}
lemma a2(n: nat) requires even(n) ensures even(n + 2) {}
lemma a3(n: nat) requires even(n + 2) ensures even(n) {}


// Dafny lacks syntax to define `Inductive` Prop like in Coq.
// We'll show two workarounds for this.

// Workaround 1: simulate with "rules"
datatype EvenRule =
  | ev_0
  | ev_SS(r: EvenRule)
{
  ghost function apply(): nat
    decreases this
  {
    match this {
      case ev_0 => 0
      case ev_SS(r) => r.apply() + 2
    }
  }
}
ghost predicate Even(n: nat) {
  exists r: EvenRule :: r.apply() == n
}
// then we can prove by "constructing" or "destructing" just like in Coq:
lemma b0() ensures Even(4) {
  var r := ev_SS(ev_SS(ev_0));
  assert r.apply() == 4;
}
lemma b1() ensures !Even(3) {
  assert forall r: EvenRule :: r.apply() != 3;
}
lemma b2(n: nat) requires Even(n) ensures Even(n + 2) {
  var r: EvenRule :| r.apply() == n;
  var r2 := ev_SS(r);
  assert r2.apply() == n + 2;
}
lemma b3(n: nat) requires Even(n + 2) ensures Even(n) {
  var r: EvenRule :| r.apply() == n + 2;
  assert r.ev_SS?;
  var r_prev := r.r;
  assert r_prev.apply() == n;
}


// Workaround 2: using "higher-order" predicates
type P = nat -> bool
ghost predicate Ev(ev: P) {
  ev(0) && (forall n: nat | ev(n) :: ev(n + 2))
}
// we explicitly say that `ev` is the "strictest" `P` that satisfies `Ev`:
ghost predicate Minimal(Ev: P -> bool, ev: P) {
  Ev(ev) && (forall ev': P, n: nat | Ev(ev') :: ev(n) ==> ev'(n))
}
// In this approach, some lemmas are a bit tricky to prove...
lemma c0(ev: P) requires Minimal(Ev, ev) ensures ev(4) {}
lemma c1(ev: P) requires Minimal(Ev, ev) ensures !ev(3) {}
lemma c2(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures ev(n + 2) {}
lemma c3(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n + 2) ensures ev(n) {}


// Finally, we "circularly" prove the equivalence among these three:
lemma a_implies_b(n: nat) requires even(n) ensures Even(n) {
  if n == 0 {
    var r := ev_0;
    assert Even(0);
  } else {
    a_implies_b(n - 2);
    var r := ev_SS(ev_SS(ev_0));
    assert Even(n);
  }
}
lemma b_implies_c(ev: P, n: nat) requires Minimal(Ev, ev) && Even(n) ensures ev(n) {
  var r: EvenRule :| r.apply() == n;
  assert ev(n);
}
lemma c_implies_a(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures even(n) {
  assert even(n);
}


type Variables
predicate Init(v: Variables)
predicate Next(v: Variables, v': Variables)

predicate Safety(v: Variables)
predicate Inv(v: Variables)

type Behavior = nat -> Variables

lemma InvHoldsTo(e: nat -> Variables, i: nat)
  requires Init(e(0))
  requires forall i:nat :: Next(e(i), e(i+1))
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(e(i))
{
  if i == 0 {
    return;
  }
  InvHoldsTo(e, i-1);
  // this is the inductive hypothesis
  // the requirements let us take the invariant from one step to the next (so in
  // particular from e(i-1) to e(i)).
}

ghost predicate IsBehavior(e: Behavior) {
  && Init(e(0))
  && forall i:nat :: Next(e(i), e(i+1))
}

lemma SafetyAlwaysHolds(e: Behavior)
  requires forall v :: Init(v) ==> Inv(v)
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  requires forall v :: Inv(v) ==> Safety(v)
  ensures IsBehavior(e) ==> forall i :: Safety(e(i))
{
  if IsBehavior(e) {
    forall i:nat
      ensures Safety(e(i)) {
      InvHoldsTo(e, i);
    }
  }
}

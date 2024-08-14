module Types {
  type Event(==, 0, !new)
}

import opened Types

module Code {
  import opened Types
  type Variables(==, 0, !new)
  ghost predicate Init(v: Variables)
  ghost predicate Next(v: Variables, v': Variables, ev: Event)

  ghost predicate IsBehavior(tr: nat -> Event) {
    exists ss: nat -> Variables ::
      && Init(ss(0))
      && forall n: nat :: Next(ss(n), ss(n + 1), tr(n))
  }
}

module Spec {
  import opened Types
  type Variables(==, 0, !new)
  ghost predicate Init(v: Variables)
  ghost predicate Next(v: Variables, v': Variables, ev: Event)

  ghost predicate IsCBehavior(tr: nat -> Event) {
    exists ss: nat -> Variables ::
      && Init(ss(0))
      && forall n: nat :: Next(ss(n), ss(n + 1), tr(n))
  }
}

ghost predicate Inv(v: Code.Variables)
ghost function Abstraction(v: Code.Variables): Spec.Variables

lemma {:axiom} AbstractionInit(v: Code.Variables)
  requires Code.Init(v)
  ensures Inv(v)
  ensures Spec.Init(Abstraction(v))

lemma {:axiom} AbstractionInductive(v: Code.Variables, v': Code.Variables, ev: Event)
  requires Inv(v)
  requires Code.Next(v, v', ev)
  ensures Inv(v')
  ensures Spec.Next(Abstraction(v), Abstraction(v'), ev)

lemma InvAt(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires Code.Init(ss(0))
  requires forall k: nat :: Code.Next(ss(k), ss(k + 1), tr(k))
  ensures Inv(ss(i))
{
  if i == 0 {
    AbstractionInit(ss(0));
  } else {
    InvAt(tr, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), tr(i - 1));
  }
}

lemma RefinementTo(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires forall n: nat :: Code.Next(ss(n), ss(n + 1), tr(n))
  requires forall n: nat :: Inv(ss(n))
  ensures forall n: nat | n < i :: Spec.Next(Abstraction(ss(n)), Abstraction(ss(n + 1)), tr(n))
{
  if i == 0 {
    return;
  } else {
    RefinementTo(tr, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), tr(i - 1));
  }
}

lemma Refinement(tr: nat -> Event)
  requires Code.IsBehavior(tr)
  ensures Spec.IsCBehavior(tr)
{
  var ss: nat -> Code.Variables :|
    && Code.Init(ss(0))
    && forall n: nat :: Code.Next(ss(n), ss(n + 1), tr(n));
  forall i: nat
    ensures Inv(ss(i))
  {
    InvAt(tr, ss, i);
  }

  var ss': nat -> Spec.Variables :=
    (i: nat) => Abstraction(ss(i));
  forall n: nat
    ensures Spec.Next(ss'(n), ss'(n + 1), tr(n))
  {
    RefinementTo(tr, ss, n+1);
  }
}

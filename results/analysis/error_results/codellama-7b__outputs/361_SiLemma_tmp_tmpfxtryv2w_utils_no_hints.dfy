
module Utils {

  lemma AllBelowBoundSize(bound: nat)
    ensures
      var below := set n : nat | n < bound :: n;
      |below| ==  bound
  {
    if bound == 0 {
    } else {
      AllBelowBoundSize(bound-1);
      var belowminus := set n : nat | n < bound-1 :: n;
      var below := set n : nat | n < bound :: n;
    }
  }

  lemma SizeOfContainedSet(a: set<nat>, b: set<nat>)
    requires forall n: nat :: n in a ==> n in b
    ensures |a| <= |b|
  {
    if |a| == 0 {
    } else {
      var y :| y in a;
      var new_a := a - {y};
      var new_b := b - {y};
      SizeOfContainedSet(new_a, new_b);
    }
  }

  lemma BoundedSetSize(bound: nat, values: set<nat>)
    requires forall n :: n in values ==> n < bound
    ensures |values| <= bound
  {
    var all_below_bound := set n : nat | n < bound :: n;
    AllBelowBoundSize(bound);
    SizeOfContainedSet(values, all_below_bound);
  }

  lemma MappedSetSize<T, U>(s: set<T>, f: T->U, t: set<U>)
    requires forall n: T, m: T :: m != n ==> f(n) != f(m)
    requires t == set n | n in s :: f(n)
    ensures |s| == |t|
  {
    var t := set n | n in s :: f(n);
    if |s| == 0 {
    } else {
      var y :| y in s;
      var new_s := s - {y};
      var new_t := t - {f(y)};
      MappedSetSize(new_s, f, new_t);
    }
  }

  lemma SetSizes<T>(a: set<T>, b: set<T>, c: set<T>)
    requires c == a + b
    requires forall t: T :: t in a ==> t !in b
    requires forall t: T :: t in b ==> t !in a
    ensures |c| == |a| + |b|
  {
    var all_in_a := set n : T | n in a :: n;
    var all_in_b := set n : T | n in b :: n;
    var all_in_c := set n : T | n in c :: n;
    var all_in_a_minus_b := set n : T | n in a && !(n in b) :: n;
    var all_in_b_minus_a := set n : T | n in b && !(n in a) :: n;
    var all_in_c_minus_a := set n : T | n in c && !(n in a) :: n;
    var all_in_c_minus_b := set n : T | n in c && !(n in b) :: n;
    var all_in_a_minus_b_plus_all_in_b_minus_a := all_in_a_minus_b + all_in_b_minus_a;
    var all_in_c_minus_a_plus_all_in_c_minus_b := all_in_c_minus_a + all_in_c_minus_b;
    var all_in_c_minus_a_plus_all_in_c_minus_b_plus_all_in_a_minus_b := all_in_c_minus_a_plus_all_in_c_minus_b + all_in_a_minus_b_plus_all_in_b_minus_a;
    var all_in_c := all_in_a + all_in_b + all_in_c_minus_a_plus_all_in_c_minus_b_plus_all_in_a_minus_b;
    assert |c| == |all_in_c|;
  }

}

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Abc = End | Wrapper(seq<Abc>)

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{
  match a {
    case Wrapper(s) =>
      assert forall x :: x in s ==> x != Wrapper([a]); // Ensuring no element in s is Wrapper([a])
    case End =>
      // No action needed for End as it trivially satisfies the postcondition
  }
}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
  match s[0] {
    case Wrapper(t) =>
      assert forall x :: x in s ==> x != Wrapper(s); // Ensuring no element in s is Wrapper(s)
    case End =>
      // No action needed for End as it trivially satisfies the postcondition
  }
}

datatype Def = End | MultiWrapper(multiset<Def>)

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
  match a {
    case MultiWrapper(ms) =>
      assert forall x :: x in ms ==> x != MultiWrapper(ms); // Ensuring no element in ms is MultiWrapper(ms)
    case End =>
      // No action needed for End as it trivially satisfies the postcondition
  }
}

datatype Ghi = End | SetWrapper(set<Ghi>)

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
  match a {
    case SetWrapper(st) =>
      assert forall x :: x in st ==> x != SetWrapper(st); // Ensuring no element in st is SetWrapper(st)
    case End =>
      // No action needed for End as it trivially satisfies the postcondition
  }
}
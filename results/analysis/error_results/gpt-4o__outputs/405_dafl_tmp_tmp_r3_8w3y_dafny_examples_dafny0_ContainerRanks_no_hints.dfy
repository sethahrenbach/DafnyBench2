// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Abc = End | Wrapper(seq<Abc>)

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{
  match a {
    case End => assert a != Wrapper([a]);
    case Wrapper(s) => assert a != Wrapper([a]);
  }
}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
  assert s[0] != Wrapper(s);
  match s[0] {
    case End => assert true;
    case Wrapper(ss) => assert ss != s;
  }
}

datatype Def = End | MultiWrapper(multiset<Def>)

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
  match a {
    case End => assert a != MultiWrapper(multiset{a});
    case MultiWrapper(ms) => assert a !in ms;
  }
}

datatype Ghi = End | SetWrapper(set<Ghi>)

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
  match a {
    case End => assert a != SetWrapper({a});
    case SetWrapper(ss) => assert a !in ss;
  }
}
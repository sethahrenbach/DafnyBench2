datatype Abc = AbcEnd | Wrapper(seq<Abc>)

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{
  if a == AbcEnd {
    assert a != Wrapper([a]);
  } else {
    assert a == Wrapper([a]);
    SeqRank0(Wrapper([a]));
  }
}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
  assert s[0] == AbcEnd || s[0] == Wrapper(s);
}

datatype Def = DefEnd | MultiWrapper(multiset<Def>)

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
  if a == DefEnd {
    assert a != MultiWrapper(multiset{a});
  } else {
    assert a == MultiWrapper(multiset{a});
    MultisetRank(MultiWrapper(multiset{a}));
  }
}

datatype Ghi = GhiEnd | SetWrapper(set<Ghi>)

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
  if a == GhiEnd {
    assert a != SetWrapper({a});
  } else {
    assert a == SetWrapper({a});
    SetRank(SetWrapper({a}));
  }
}
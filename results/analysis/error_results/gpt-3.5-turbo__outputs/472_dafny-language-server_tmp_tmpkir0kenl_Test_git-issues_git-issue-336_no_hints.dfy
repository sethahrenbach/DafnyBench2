
lemma TestMap(a: map<int, (int,int)>)
  ensures forall k :: k in a ==> k in (map k | k in a :: a[k].0)
{
  assert forall k :: k in a <==> k in (map k | k in a :: a[k].0);
}

lemma TestSet0(a: set<int>)
  ensures a == (set k | k in a && k < 7)
{
  assert forall k :: k in a <==> k in (set k | k in a && k < 7);
}

lemma TestSet1(a: set<int>, m: int)
  ensures a == (set k | k in a && k < 7 :: m + (k - m))
{
  assert forall k :: k in a <==> k in (set k | k in a && k < 7);
  assert a == (set k | k in a && k < 7 :: m + (k - m));
}

lemma TestSet2(a: set<int>, m: int)
  requires m in a && m < 7
  ensures a == (set k | k in a :: if k < 7 then k else m)
{
  assert m in a && m < 7;
  assert forall k :: k in a <==> k in (set k | k in a && k < 7);
  assert a == (set k | k in a :: if k < 7 then k else m);
}

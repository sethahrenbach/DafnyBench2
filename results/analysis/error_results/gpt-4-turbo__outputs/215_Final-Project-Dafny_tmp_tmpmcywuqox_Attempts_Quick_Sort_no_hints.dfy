
predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  var i := 0;
  while (i < |Seq|)
    invariant 0 <= i <= |Seq|
    invariant multiset(Seq_1) + multiset(Seq_2) + multiset(Seq[i..]) == multiset(Seq)
    invariant forall x | x in Seq_1 :: x <= thres
    invariant forall x | x in Seq_2 :: x >= thres
    invariant |Seq_1| + |Seq_2| + |Seq[i..]| == |Seq|
  {
    if (Seq[i] <= thres) {
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
    }
    i := i + 1;
  }
}


lemma Lemma_1(Seq_1:seq<int>,Seq_2:seq<int>)
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2
{
  forall x | x in Seq_1
    ensures x in multiset(Seq_1)
  {
    var i := 0;
    while (i < |Seq_1|)
      invariant 0 <= i <= |Seq_1|
    {
      i := i + 1;
    }
  }
}



method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
{
  if |Seq| == 0 {
    return [];
  } else if |Seq| == 1 {
    return Seq;
  } else {  
    var pivot := Seq[0];
    var Seq_1, Seq_2 := threshold(pivot, Seq[1..]);
    var Seq_1' := quickSort(Seq_1);
    var Seq_2' := quickSort(Seq_2);
    Seq' := Seq_1' + [pivot] + Seq_2';
    assert multiset(Seq_1') + multiset([pivot]) + multiset(Seq_2') == multiset(Seq);
    return Seq';
  }
}

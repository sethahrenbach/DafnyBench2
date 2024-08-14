
method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq') == multiset(Seq)
  ensures forall x :: x in Seq' ==> x <= Seq'[0]
  ensures forall x :: x in Seq' ==> x >= Seq'[0]
{
  if Seq.size() <= 1 {
    return Seq;
  }

  var pivot := Seq[0];
  var less := Seq.filter(x | x < pivot);
  var greater := Seq.filter(x | x >= pivot);

  return quickSort(less) + [pivot] + quickSort(greater);
}

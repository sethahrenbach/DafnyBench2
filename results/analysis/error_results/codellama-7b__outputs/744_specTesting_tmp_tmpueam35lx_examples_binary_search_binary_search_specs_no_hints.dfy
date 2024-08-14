
lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
  requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
{
  var lo:nat := 0;
  var hi:nat := |intSeq|;
  while lo < hi
  {
    var mid := (lo + hi) / 2;
    if intSeq[mid] < key
    {
      lo := mid + 1;
    }
    else if intSeq[mid] > key
    {
      hi := mid;
    }
    else
    {
      return mid;
    }
  }
  return -1;
}

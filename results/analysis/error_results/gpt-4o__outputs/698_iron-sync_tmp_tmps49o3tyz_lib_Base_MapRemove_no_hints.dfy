module {:extern} MapRemove_s {
  function {:opaque} MapRemove1<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures forall j :: j in m && j != k ==> j in m'
    ensures forall j :: j in m' ==> j in m && j != k
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures k in m ==> |m'| == |m| - 1
    ensures k !in m ==> |m'| == |m|
  {
    var m' := map j | j in m && j != k :: m[j];
    m'
  }

  method {:extern "MapRemove__s_Compile", "ComputeMapRemove1"}
      ComputeMapRemove1<K,V>(m: map<K,V>, k:K) 
  returns (m' : map<K,V>)
  ensures m' == MapRemove1(m, k)
  {
    m' := MapRemove1(m, k);
    assert forall j :: j in m && j != k ==> j in m';
    assert forall j :: j in m' ==> j in m && j != k;
    assert forall j :: j in m' ==> m'[j] == m[j];
    assert |m'.Keys| <= |m.Keys|;
    assert k in m ==> |m'| == |m| - 1;
    assert k !in m ==> |m'| == |m|;
  }
}
module UtilitiesLibrary {
  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {
    theSeq[..|theSeq|-1]
  }

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {
    theSeq[|theSeq|-1]
  }

  function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
    decreases |theSets|
  {
    if |theSets| == 0 then {} else
      UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  lemma SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
  {
    if |theSets| == 0 {
    } else {
      SetsAreSubsetsOfUnion(DropLast(theSets));
      assert forall idx | 0 <= idx < |DropLast(theSets)| :: DropLast(theSets)[idx] <= UnionSeqOfSets(DropLast(theSets));
      assert Last(theSets) <= UnionSeqOfSets(theSets);
    }
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member: T | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
  {
    if |theSets| == 0 {
      assert forall member: T | member in {} :: false;
    } else {
      EachUnionMemberBelongsToASet(DropLast(theSets));
      assert forall member: T | member in UnionSeqOfSets(DropLast(theSets)) ::
            exists idx :: 0 <= idx < |DropLast(theSets)| && member in DropLast(theSets)[idx];
      assert forall member: T | member in Last(theSets) ::
            exists idx :: idx == |theSets|-1 && member in theSets[idx];
    }
  }

  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx:int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0<=idx<|theSets|
    ensures member in theSets[idx]
  {
    EachUnionMemberBelongsToASet(theSets);
    var chosenIdx :| 0<=chosenIdx<|theSets| && member in theSets[chosenIdx];
    idx := chosenIdx;
  }

  datatype Option<T> = Some(value:T) | None

  function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j != key :: m[j];
    m'
  }

  datatype Direction = North() | East() | South() | West()

  function TurnRight(direction:Direction) : Direction
  {
    if direction.North?
      then East
    else if direction.East?
      then South
    else if direction.South?
      then West
    else  // By elimination, West!
      North
  }

  lemma Rotation()
  {
  }

  function TurnLeft(direction:Direction) : Direction
  {
    match direction {
      case North => West
      case West => South
      case South => East
      case East => North
    }
  }

  datatype Meat = Salami | Ham
  datatype Cheese = Provolone | Swiss | Cheddar | Jack
  datatype Veggie = Olive | Onion | Pepper
  datatype Order =
      Sandwich(meat:Meat, cheese:Cheese)
    | Pizza(meat:Meat, veggie:Veggie)
    | Appetizer(cheese:Cheese)
}

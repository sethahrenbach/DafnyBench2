module UtilitiesLibrary {
  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
    ensures |DropLast(theSeq)| == |theSeq| - 1
    ensures forall i :: 0 <= i < |DropLast(theSeq)| ==> DropLast(theSeq)[i] == theSeq[i]
  {
    theSeq[..|theSeq|-1]
  }

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
    ensures Last(theSeq) == theSeq[|theSeq|-1]
  {
    theSeq[|theSeq|-1]
  }

  function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
    ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
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
      assert forall idx | 0 <= idx < |DropLast(theSets)| :: theSets[idx] <= UnionSeqOfSets(DropLast(theSets));
      assert theSets[|theSets|-1] <= UnionSeqOfSets(theSets);
    }
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
  {
    if |theSets| == 0 {
    } else {
      EachUnionMemberBelongsToASet(DropLast(theSets));
      assert forall member | member in UnionSeqOfSets(DropLast(theSets)) ::
          exists idx :: 0<=idx<|DropLast(theSets)| && member in theSets[idx];
      assert forall member | member in Last(theSets) ::
          member in theSets[|theSets|-1];
      assert forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx];
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
    ensures (direction == North() ==> TurnRight(direction) == East()) &&
            (direction == East() ==> TurnRight(direction) == South()) &&
            (direction == South() ==> TurnRight(direction) == West()) &&
            (direction == West() ==> TurnRight(direction) == North())
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
    ensures TurnRight(TurnRight(TurnRight(TurnRight(North())))) == North()
    ensures TurnRight(TurnRight(TurnRight(TurnRight(East())))) == East()
    ensures TurnRight(TurnRight(TurnRight(TurnRight(South())))) == South()
    ensures TurnRight(TurnRight(TurnRight(TurnRight(West())))) == West()
  {
    assert TurnRight(TurnRight(TurnRight(TurnRight(North())))) == North();
    assert TurnRight(TurnRight(TurnRight(TurnRight(East())))) == East();
    assert TurnRight(TurnRight(TurnRight(TurnRight(South())))) == South();
    assert TurnRight(TurnRight(TurnRight(TurnRight(West())))) == West();
  }

  function TurnLeft(direction:Direction) : Direction
    ensures (direction == North() ==> TurnLeft(direction) == West()) &&
            (direction == West() ==> TurnLeft(direction) == South()) &&
            (direction == South() ==> TurnLeft(direction) == East()) &&
            (direction == East() ==> TurnLeft(direction) == North())
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
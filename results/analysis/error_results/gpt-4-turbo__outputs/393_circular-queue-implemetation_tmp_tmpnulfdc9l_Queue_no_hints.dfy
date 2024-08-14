class {:autocontracts} Queue {

  var circularQueue: array<int>;
  var rear: nat;
  var front: nat;
  var counter: nat;

  ghost var Content: seq<int>;

  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
  }

  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == []
    ensures counter == 0
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    counter := 0;
  }

  method insert(item: int)
    requires rear <= circularQueue.Length
    ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
        (
          Content == [item] &&
          |Content| == 1
        )
    ensures circularQueue.Length != 0 ==>
    (
      (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
        (
          Content == old(Content) &&
          |Content| == old(|Content|)
        )
    ||
      (front == 0 && rear == circularQueue.Length-1 ) ==> 
        (
          Content == old(Content) + [item] &&
          |Content| == old(|Content|) + 1
        )
    ||
      (rear + 1 != front && rear != circularQueue.Length-1 && rear + 1 < circularQueue.Length - 1) ==> 
        (
          Content == old(Content[0..rear]) + [item] + old(Content[rear..circularQueue.Length])
        )
    ||
      (rear + 1 == front) ==> 
      (
        Content[0..rear + 1] == old(Content[0..rear]) + [item] &&
        forall i :: rear + 2 <= i < circularQueue.Length ==> Content[i] == old(Content[i-1])
      )
    )
  {
  }

  method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
  {
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [1];
    queueInsert[0] := item;
    circularQueue := queueInsert;
    Content := [item];
    rear := 1;
  }

  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length-1 && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == 0
    ensures counter == old(counter) + 1
  {
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [circularQueue.Length + 1];
    var i: nat := 0;
    while i < circularQueue.Length
      invariant circularQueue.Length + 1 == queueInsert.Length
      invariant 0 <= i <= circularQueue.Length
      invariant forall j :: 0 <= j < i ==> queueInsert[j] == circularQueue[j]
    {
      queueInsert[i] := circularQueue[i];
      i := i + 1;
    }
    queueInsert[queueInsert.Length - 1] := item;
    Content := Content + [item];
    rear := 0;  // Reset rear to the start as it's circular
    circularQueue := queueInsert;
  }

  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1
  {
    counter := counter + 1;
    circularQueue[rear] := item;
    rear := (rear + 1) % circularQueue.Length;
    Content := old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length]);
  }

  method auxInsertInitQueue(item:int)
  {
  }

  method auxInsertBetweenQueue(item:int)
  {
  }

  method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[old(front)]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[old(front)..rear]
    ensures old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|]
  {
    if counter == 0 {
      item := -1;
    } else {
      item := circularQueue[front];
      front := (front + 1) % circularQueue.Length;
      counter := counter - 1;
    }
  }

  method size() returns (size:nat)
    ensures size == counter
  {
    size := counter;
  }

  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> counter == 0;
    ensures isEmpty == false ==> counter != 0;
  {
    isEmpty := if counter == 0 then true else false;
  }

  method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
  {
    var i: nat := 0;
    contains := false;

    while (i < circularQueue.Length)
    {
      if (circularQueue[i] == item) {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }

  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue) 
  {
    var newQueueSize : int := otherQueue.circularQueue.Length + circularQueue.Length;
    var newFront: int := front;
    var newRear: int := otherQueue.rear;

    var tmp: array<int> := new int[newQueueSize];

    forall i | 0 <= i < circularQueue.Length
    { 
      tmp[i] := circularQueue[i];
    }

    mergedQueue := new Queue(); 
  }
}

method Main ()
{
  var circularQueue := new Queue();

  var isQueueEmpty := circularQueue.isEmpty();

  var queueSize := circularQueue.size();

  circularQueue.auxInsertEmptyQueue(2);

  circularQueue.auxInsertEndQueue(4);

  circularQueue.auxInsertEndQueue(4);

  circularQueue.auxInsertEndQueue(56);

  var contains56 := circularQueue.contains(56);

  var contains4 := circularQueue.contains(4);

  var item := circularQueue.remove();
}
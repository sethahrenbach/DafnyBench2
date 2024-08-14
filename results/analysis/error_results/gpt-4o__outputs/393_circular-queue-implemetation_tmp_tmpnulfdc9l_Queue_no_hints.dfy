class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
  }

  // Construtor
  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == [] // REVISAR
    ensures counter == 0
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    counter := 0;
  } //[tam] ; [1, 2, 3, 4]

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
          Content == old(Content)  &&
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
        forall i :: rear + 2 <= i <= circularQueue.Length ==> Content[i] == old(Content[i-1])
      )
    )
    {
      if front == 0 && rear == 0 && circularQueue.Length == 0 {
        auxInsertEmptyQueue(item);
      } else if front == 0 && rear == circularQueue.Length-1 && circularQueue.Length > 0 {
        auxInsertEndQueue(item);
      } else if rear < front && front < circularQueue.Length {
        auxInsertSpaceQueue(item);
      } else if rear == front && circularQueue.Length > 0 {
        auxInsertInitQueue(item);
      } else {
        auxInsertBetweenQueue(item);
      }
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
    queueInsert := new int [circularQueue.Length + 1];
    queueInsert[0] := item;
    circularQueue := queueInsert;
    Content := [item];
    rear := rear + 1;
  }

  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
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
    rear := rear + 1;
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
    var newCircularQueue: array<int> := new int[circularQueue.Length];
    var i: nat := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant forall j :: 0 <= j < i ==> newCircularQueue[j] == circularQueue[j]
    {
      newCircularQueue[i] := circularQueue[i];
      i := i + 1;
    }
    newCircularQueue[rear] := item;
    circularQueue := newCircularQueue;
    Content := old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length]);
    rear := rear + 1;
  }

  method auxInsertInitQueue(item:int)
    requires rear == front && circularQueue.Length > 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1
  {
    counter := counter + 1;
    var newCircularQueue: array<int> := new int[circularQueue.Length];
    var i: nat := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant forall j :: 0 <= j < i ==> newCircularQueue[j] == circularQueue[j]
    {
      newCircularQueue[i] := circularQueue[i];
      i := i + 1;
    }
    newCircularQueue[rear] := item;
    circularQueue := newCircularQueue;
    Content := old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length]);
    rear := rear + 1;
  }

  method auxInsertBetweenQueue(item:int)
    requires rear < circularQueue.Length && rear + 1 != front
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1
  {
    counter := counter + 1;
    var newCircularQueue: array<int> := new int[circularQueue.Length];
    var i: nat := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant forall j :: 0 <= j < i ==> newCircularQueue[j] == circularQueue[j]
    {
      newCircularQueue[i] := circularQueue[i];
      i := i + 1;
    }
    newCircularQueue[rear] := item;
    circularQueue := newCircularQueue;
    Content := old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length]);
    rear := rear + 1;
  }

  // remove apenas mudando o ponteiro
  // sem resetar o valor na posição, pois, provavelmente,
  // vai ser sobrescrito pela inserção
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
      if old(front) < rear {
        Content := old(Content)[old(front)..rear];
      } else {
        Content := old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|];
      }
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
      invariant 0 <= i <= circularQueue.Length
      invariant contains == true ==> item in circularQueue[..i]
      invariant contains == false ==> item !in circularQueue[..i]
    {
      if (circularQueue[i] == item) {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }

  // TODO
  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue) 
  {
    var newQueueSize : int := otherQueue.circularQueue.Length + circularQueue.Length;
    var newFront: int := front;
    var newRear: int := otherQueue.rear;

    var tmp: array<int> := new int[newQueueSize];

    forall i | 0 <= i < circularQueue.Length
      ensures tmp[i] == circularQueue[i]
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
  //assert circularQueue.Content == [2, 4, 4, 56];
}
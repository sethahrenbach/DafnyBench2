// A LIFO queue (aka a stack) with limited capacity.
class LimitedStack {
  
  var capacity: int; // capacity, max number of elements allowed on the stack.
  var arr: array<int>; // contents of stack.
  var top: int; // The index of the top of the stack, or -1 if the stack is empty

  // This predicate express a class invariant: All objects of this class should satisfy this.
  predicate Valid()
    reads this
  {
    arr != null && capacity > 0 && capacity == arr.Length && top >= -1 && top < capacity
  }

  predicate Empty()
    reads this`top
  {
    top == -1
  }

  predicate Full()
    reads this`top, this`capacity
  {
    top == (capacity - 1)
  }

  method Init(c: int)
    modifies this
    requires c > 0
    ensures Valid() && Empty() && c == capacity
    ensures fresh(arr) // ensures arr is a newly created object.
  {
    capacity := c;
    arr := new int[c];
    top := -1;
  }

  method isEmpty() returns (res: bool)
    ensures res == Empty()
  {
    return top == -1;
  }

  method Peek() returns (elem: int)
    requires Valid() && !Empty()
    ensures elem == arr[top]
  {
    return arr[top];
  }

  method Push(elem: int)
    modifies this`top, this.arr
    requires Valid()
    requires !Full()
    ensures Valid() && top == old(top) + 1 && arr[top] == elem
    ensures !old(Empty()) ==> forall i: int :: 0 <= i <= old(top) ==> arr[i] == old(arr[i])
  {
    top := top + 1;
    arr[top] := elem;
  }

  method Pop() returns (elem: int)
    modifies this`top
    requires Valid() && !Empty()
    ensures Valid() && top == old(top) - 1
    ensures elem == arr[old(top)]
  {
    elem := arr[top];
    top := top - 1;
    return elem;
  }

  method Shift()
    requires Valid() && !Empty()
    ensures Valid()
    ensures forall i: int :: 0 <= i < capacity - 1 ==> arr[i] == old(arr[i + 1])
    ensures top == old(top) - 1
    modifies this.arr, this`top
  {
    var i: int := 0;
    while (i < top)
      invariant 0 <= i <= top
      invariant forall j: int :: 0 <= j < i ==> arr[j] == old(arr[j + 1])
    {
      arr[i] := arr[i + 1];
      i := i + 1;
    }
    top := top - 1;
  }

  method Push2(elem: int)
    modifies this.arr, this`top
    requires Valid()
    ensures Valid() && !Empty()
    ensures arr[top] == elem
    ensures old(!Full()) ==> top == old(top) + 1
    ensures old(Full()) ==> forall i: int :: 0 <= i < capacity - 1 ==> arr[i] == old(arr[i + 1])
  {
    if (Full()) {
      Shift();
    }
    if (top < capacity - 1) {
      top := top + 1;
    }
    arr[top] := elem;
  }

  method Main() {
    var s := new LimitedStack;
    s.Init(3);

    s.Push(27);

    var e := s.Pop();

    s.Push(5);

    s.Push(32);
    s.Push(9);

    var e2 := s.Pop();

    s.Push(e2);
    s.Push2(99);

    var e3 := s.Peek();
  }
}
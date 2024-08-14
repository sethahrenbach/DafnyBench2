
class LimitedStack {
  var capacity: int;
  var arr: array<int>;
  var top: int;

  constructor(c: int) {
    capacity = c;
    arr = new array<int>(c);
    top = -1;
  }

  method Push(x: int) {
    if (top == capacity - 1) {
      Shift();
    }
    top = top + 1;
    arr[top] = x;
  }

  method Pop(): int {
    if (top == -1) {
      return null;
    }
    top = top - 1;
    return arr[top + 1];
  }

  method Shift() {
    var i: int = 0;
    while (i < top) {
      arr[i] = arr[i + 1];
      i = i + 1;
    }
    top = top - 1;
  }

  method isEmpty(): bool {
    return top == -1;
  }

  method isFull(): bool {
    return top == capacity - 1;
  }

  method size(): int {
    return top + 1;
  }

  method capacity(): int {
    return capacity;
  }

  method toString(): string {
    var s: string = "";
    for (i: int = 0; i <= top; i++) {
      s = s + arr[i].toString() + " ";
    }
    return s;
  }
}


module Rope {
  class Node {
    var data: byte;
    var next: Node;
  }

  var head: Node;
  var tail: Node;

  function insert(i: nat, c: byte): void {
    require i >= 0 && i <= length;
    var newNode = new Node();
    newNode.data = c;
    newNode.next = head;
    head = newNode;
  }

  function delete(i: nat): void {
    require i >= 0 && i < length;
    var currentNode = head;
    var previousNode = null;
    while (currentNode != null && i > 0) {
      previousNode = currentNode;
      currentNode = currentNode.next;
      i--;
    }
    if (currentNode != null) {
      if (previousNode == null) {
        head = currentNode.next;
      } else {
        previousNode.next = currentNode.next;
      }
      currentNode.next = null;
    }
  }

  function get(i: nat): byte {
    require i >= 0 && i < length;
    var currentNode = head;
    while (currentNode != null && i > 0) {
      currentNode = currentNode.next;
      i--;
    }
    return currentNode.data;
  }

  function set(i: nat, c: byte): void {
    require i >= 0 && i < length;
    var currentNode = head;
    while (currentNode != null && i > 0) {
      currentNode = currentNode.next;
      i--;
    }
    currentNode.data = c;
  }

  function length(): nat {
    var currentNode = head;
    var length = 0;
    while (currentNode != null) {
      length++;
      currentNode = currentNode.next;
    }
    return length;
  }
}

class A {
  var value: int
  constructor ()
     ensures value == 10
  {
     value := 10;
  }
}

class B {
   var a: A
   constructor () { a := new A(); }

   method m()
     requires a.value == 11
     modifies this, this.a
   {
     var oldA := a;
     label L:
     assert a.value == 11;
     a.value := 12;
     assert a.value == 12;
     label M:
     a := new A(); // Line X
     assert a.value == 10;
     assert oldA.value == 12; // Ensure the old reference's value is still 12
     label N:
     a.value := 20;
     assert a.value == 20;
     label P:
     assert a.value == 20;
     assert oldA.value == 12; // Ensure the old reference's value is still 12
                                // but .value in current state
                                  // reference at Line X
  }
}
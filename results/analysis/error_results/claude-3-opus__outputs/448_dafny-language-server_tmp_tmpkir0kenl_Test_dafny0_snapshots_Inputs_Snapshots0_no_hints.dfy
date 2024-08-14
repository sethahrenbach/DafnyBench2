method foo()
{
  // Since bar() has a postcondition of false, it means 
  // bar() is not allowed to terminate normally. So foo()
  // also cannot terminate normally after calling bar().
}

method bar()
  ensures false;
{
  // bar() has a postcondition of false, so it cannot
  // terminate normally. 
  // One way to achieve this is to explicitly indicate
  // failure using the 'assert false' statement.
  assert false;
}
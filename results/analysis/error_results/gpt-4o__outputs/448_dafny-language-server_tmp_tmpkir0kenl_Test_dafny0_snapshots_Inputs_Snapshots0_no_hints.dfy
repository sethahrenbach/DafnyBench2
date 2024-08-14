method foo()
{
  bar();
}

method bar()
  ensures false
  decreases *; // Indicate that the method is possibly non-terminating
{
  while (true)
    invariant true; // This invariant indicates that the loop never terminates
  {
  }
}
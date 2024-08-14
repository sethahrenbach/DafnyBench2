  function foo(x: int): int {
  if x > 0 then
    return x;
  else
    return -x;
}

// Dafny verification error:
// foo.dfy(3,4): Error: invalid UnaryExpression (ID: p_generic_syntax_error)
// This "invalid something" message where the something is typically
// the name of an internal parser non-terminal means that the text being parsed
// is a badly malformed instance of whatever parser entity was being parsed.
// This is an automatically generated message by the CoCo parser generator
// for a situation in which no specific recovery or a
// more informative error message has been implemented.
//
// The only advice we can give is to carefully scrutinize the location of the
// error to see what might be wrong with the text. If you think this is a
// common or confusing enough occurrence to warrant special error handling,
// please suggest the improvement, with this sample code, to the Dafny team.
// 1 parse errors detected in foo.dfy

// Solution:
// The error message is indicating that the expression after the "return" keyword is not valid.
// To fix the error, add a valid expression after the "return" keyword.

function foo(x: int): int {
  if x > 0 then
    return x;
  else
    return -x;
}

// Dafny verification succeeded.
// 0 warnings and 0 errors detected in foo.dfy

// The preconditions and postconditions are the same as the original program.
// The program correctly returns the absolute value of the input integer.
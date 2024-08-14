method main(x: int, y: int) returns (x_out: int, y_out: int, n: int)
requires x >= 0
requires y >= 0
requires x == y
ensures y_out == n
{
    x_out := x;
    y_out := y;
    n := 0;

    // Loop invariant: 
    // - x_out and y_out decrease by the same amount in each iteration
    // - x_out, y_out >= 0
    // - x_out == y_out
    // - n increases by 1 in each iteration, starting from 0
    // - n == x - x_out == y - y_out
    while (x_out > 0)
        invariant x_out >= 0
        invariant y_out >= 0 
        invariant x_out == y_out
        invariant n >= 0
        invariant n == x - x_out == y - y_out
        decreases x_out
    {
        x_out := x_out - 1;
        y_out := y_out - 1;
        n := n + 1;
    }

    // Loop termination is proved by the decreases clause:
    // - x_out is decreased by 1 in each iteration
    // - x_out is bounded below by 0 due to the invariant x_out >= 0
    // - Therefore, the loop will eventually terminate
    
    // Postcondition y_out == n is proved as follows:
    // - Loop terminates when x_out == 0
    // - Loop invariant ensures n == x - x_out == y - y_out
    // - Therefore, when x_out == 0, we have n == x == y
    // - Also, loop invariant ensures x_out == y_out
    // - So when x_out == 0, we also have y_out == 0
    // - Therefore, y_out == 0 == x == y == n at the end
}
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

method {:testEntry} ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0; 
    while x != N
        invariant 0 <= x <= N 
        invariant y == Power(x) 
        decreases N - x
    {
        x, y := x + 1, y + y;
    } 
}

method {:test} Test9() {
expect 2448 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2448);
expect r0 == Power(2448);
}

// REPEAT 10 - TIME: 11.0636202 s

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

method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(4);
expect r0 == Power(4);
}

// REPEAT 4 - TIME: 4.1407926 s

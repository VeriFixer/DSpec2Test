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

method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(8);
expect r0 == Power(8);
}

// REPEAT 8 - TIME: 6.8354927 s

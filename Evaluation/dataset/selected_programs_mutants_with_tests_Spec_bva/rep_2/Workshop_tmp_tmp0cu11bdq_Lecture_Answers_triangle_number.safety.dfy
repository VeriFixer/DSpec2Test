method {:testEntry} TriangleNumber(N: int) returns (t: int)
    requires N >= 0
    ensures t == N * (N + 1) / 2
{
    t := 0;
    var n := 0;
    while n < N
        invariant 0 <= n <= N
        invariant t == n * (n + 1) / 2
        decreases N - n;// can be left out because it is guessed correctly by Dafny
    {
        n:= n + 1;
        t := t + n;
    }
}

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(101);
expect r0 == 101 * (101 + 1) / 2;
}

// REPEAT 2 - TIME: 5.5550218 s

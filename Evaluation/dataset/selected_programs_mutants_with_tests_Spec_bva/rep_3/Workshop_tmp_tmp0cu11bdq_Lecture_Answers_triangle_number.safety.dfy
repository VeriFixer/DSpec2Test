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

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(102);
expect r0 == 102 * (102 + 1) / 2;
}

// REPEAT 3 - TIME: 7.5471614 s

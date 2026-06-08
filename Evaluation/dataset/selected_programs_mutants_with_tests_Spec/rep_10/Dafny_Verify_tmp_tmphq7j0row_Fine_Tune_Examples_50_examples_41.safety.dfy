method {:testEntry} main(n: int, k: int) returns (i :int, j: int)
    requires n >= 0
    requires k == 1 || k >= 0
    ensures k + i + j >= 2 * n
{
    i := 0;
    j := 0;
    while(i < n)
        invariant 0 <= i <= n
        invariant j == i * (i + 1) / 2
    {
        i := i + 1;
        j := j + i;
    }
}

method {:test} Test10() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 11 == 1 || 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7728, 11);
expect 11 + r0 + r1 >= 2 * 7728;
}

// REPEAT 10 - TIME: 7.4291518 s

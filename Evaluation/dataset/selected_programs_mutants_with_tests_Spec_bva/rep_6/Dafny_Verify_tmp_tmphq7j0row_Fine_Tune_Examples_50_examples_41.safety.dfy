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

method {:test} Test28() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105 == 1 || 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7724, 105);
expect 105 + r0 + r1 >= 2 * 7724;
}

// REPEAT 6 - TIME: 12.4492407 s

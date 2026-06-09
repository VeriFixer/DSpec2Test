method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test14() {
expect 37450465281508189576483680376842270 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842270);
expect r0 == 37450465281508189576483680376842270 * (7 * 37450465281508189576483680376842270 - 5) / 2;
}

// REPEAT 10 - TIME: 43.3296139 s

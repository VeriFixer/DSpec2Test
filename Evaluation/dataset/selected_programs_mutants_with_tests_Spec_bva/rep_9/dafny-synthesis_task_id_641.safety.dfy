method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test13() {
expect 37450465281508189576483680376842269 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842269);
expect r0 == 37450465281508189576483680376842269 * (7 * 37450465281508189576483680376842269 - 5) / 2;
}

// REPEAT 9 - TIME: 43.7968154 s

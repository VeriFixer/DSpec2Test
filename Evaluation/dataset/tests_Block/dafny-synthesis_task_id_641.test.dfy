method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(0);
expect r0 == 0 * (7 * 0 - 5) / 2;
}

// REPEAT 1 - TIME: 2.4619123 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(1);
expect r0 == 1 * (7 * 1 - 5) / 2;
}

// REPEAT 2 - TIME: 3.4357985 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(2);
expect r0 == 2 * (7 * 2 - 5) / 2;
}

// REPEAT 3 - TIME: 4.1230263 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(3);
expect r0 == 3 * (7 * 3 - 5) / 2;
}

// REPEAT 4 - TIME: 4.8197831 s

method {:test} Test4() {
expect 738 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(738);
expect r0 == 738 * (7 * 738 - 5) / 2;
}

// REPEAT 5 - TIME: 5.5328021 s

method {:test} Test5() {
expect 739 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(739);
expect r0 == 739 * (7 * 739 - 5) / 2;
}

// REPEAT 6 - TIME: 6.2417359 s


// REPEAT 7 - TIME: 36.5023737 s


// REPEAT 8 - TIME: 66.7145216 s


// REPEAT 9 - TIME: 96.8190629 s


// REPEAT 10 - TIME: 126.9218187 s

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

// REPEAT 1 - TIME: 2.371313 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(1);
expect r0 == 1 * (7 * 1 - 5) / 2;
}

// REPEAT 2 - TIME: 3.1720201 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(2);
expect r0 == 2 * (7 * 2 - 5) / 2;
}

// REPEAT 3 - TIME: 4.1367493 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(3);
expect r0 == 3 * (7 * 3 - 5) / 2;
}

// REPEAT 4 - TIME: 4.9988765 s

method {:test} Test4() {
expect 738 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(738);
expect r0 == 738 * (7 * 738 - 5) / 2;
}

// REPEAT 5 - TIME: 5.8646512 s

method {:test} Test5() {
expect 739 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(739);
expect r0 == 739 * (7 * 739 - 5) / 2;
}

// REPEAT 6 - TIME: 6.7507374 s


// REPEAT 7 - TIME: 37.0955458 s


// REPEAT 8 - TIME: 67.3603765 s


// REPEAT 9 - TIME: 97.4737445 s


// REPEAT 10 - TIME: 127.5953497 s

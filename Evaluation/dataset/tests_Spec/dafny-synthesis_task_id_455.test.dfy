method {:testEntry} MonthHas31Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
{
    result := month in {1, 3, 5, 7, 8, 10, 12};
}

method {:test} Test0() {
expect 1 <= 1 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(1);
expect r0 <==> 1 in {1, 3, 5, 7, 8, 10, 12};
}
method {:test} Test1() {
expect 1 <= 3 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(3);
expect r0 <==> 3 in {1, 3, 5, 7, 8, 10, 12};
}
method {:test} Test2() {
expect 1 <= 5 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(5);
expect r0 <==> 5 in {1, 3, 5, 7, 8, 10, 12};
}
method {:test} Test3() {
expect 1 <= 7 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(7);
expect r0 <==> 7 in {1, 3, 5, 7, 8, 10, 12};
}
method {:test} Test4() {
expect 1 <= 8 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(8);
expect r0 <==> 8 in {1, 3, 5, 7, 8, 10, 12};
}
method {:test} Test5() {
expect 1 <= 10 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(10);
expect r0 <==> 10 in {1, 3, 5, 7, 8, 10, 12};
}
method {:test} Test6() {
expect 1 <= 12 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(12);
expect r0 <==> 12 in {1, 3, 5, 7, 8, 10, 12};
}
method {:test} Test7() {
expect 1 <= 11 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(11);
expect r0 <==> 11 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 1 - TIME: 5.3134255 s

method {:test} Test8() {
expect 1 <= 9 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(9);
expect r0 <==> 9 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 2 - TIME: 8.1941395 s

method {:test} Test9() {
expect 1 <= 6 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(6);
expect r0 <==> 6 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 3 - TIME: 10.5483505 s

method {:test} Test10() {
expect 1 <= 4 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(4);
expect r0 <==> 4 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 4 - TIME: 12.8295368 s

method {:test} Test11() {
expect 1 <= 2 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(2);
expect r0 <==> 2 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 5 - TIME: 14.5639049 s


// REPEAT 6 - TIME: 16.3986941 s


// REPEAT 7 - TIME: 18.3514219 s


// REPEAT 8 - TIME: 20.176224 s


// REPEAT 9 - TIME: 22.1520528 s


// REPEAT 10 - TIME: 23.9843648 s

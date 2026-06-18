method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(0);
expect r0 == 6 * 0 * (0 - 1) + 1;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(100);
expect r0 == 6 * 100 * (100 - 1) + 1;
}

// REPEAT 1 - TIME: 5.2618199 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(101);
expect r0 == 6 * 101 * (101 - 1) + 1;
}

// REPEAT 2 - TIME: 6.2171039 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(102);
expect r0 == 6 * 102 * (102 - 1) + 1;
}

// REPEAT 3 - TIME: 7.1005568 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(103);
expect r0 == 6 * 103 * (103 - 1) + 1;
}

// REPEAT 4 - TIME: 7.856707 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(104);
expect r0 == 6 * 104 * (104 - 1) + 1;
}

// REPEAT 5 - TIME: 8.7861827 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(105);
expect r0 == 6 * 105 * (105 - 1) + 1;
}

// REPEAT 6 - TIME: 9.4753874 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(106);
expect r0 == 6 * 106 * (106 - 1) + 1;
}

// REPEAT 7 - TIME: 10.0696865 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(107);
expect r0 == 6 * 107 * (107 - 1) + 1;
}

// REPEAT 8 - TIME: 10.7047973 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(108);
expect r0 == 6 * 108 * (108 - 1) + 1;
}

// REPEAT 9 - TIME: 11.3910004 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(109);
expect r0 == 6 * 109 * (109 - 1) + 1;
}

// REPEAT 10 - TIME: 12.0432053 s

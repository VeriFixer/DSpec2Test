// dafny-synthesis_task_id_80.dfy

method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
  requires n >= 0
  ensures t == n * (n + 1) * (n + 2) / 6
{
  t := n * (n + 1) * (n + 2) * 6;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(0);
expect r0 == 0 * (0 + 1) * (0 + 2) / 6;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(100);
expect r0 == 100 * (100 + 1) * (100 + 2) / 6;
}

// REPEAT 1 - TIME: 5.0495815 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(101);
expect r0 == 101 * (101 + 1) * (101 + 2) / 6;
}

// REPEAT 2 - TIME: 5.8654646 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(102);
expect r0 == 102 * (102 + 1) * (102 + 2) / 6;
}

// REPEAT 3 - TIME: 6.7217718 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(103);
expect r0 == 103 * (103 + 1) * (103 + 2) / 6;
}

// REPEAT 4 - TIME: 7.4721677 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(104);
expect r0 == 104 * (104 + 1) * (104 + 2) / 6;
}

// REPEAT 5 - TIME: 8.3090847 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(105);
expect r0 == 105 * (105 + 1) * (105 + 2) / 6;
}

// REPEAT 6 - TIME: 9.056657 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(106);
expect r0 == 106 * (106 + 1) * (106 + 2) / 6;
}

// REPEAT 7 - TIME: 9.6379103 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(107);
expect r0 == 107 * (107 + 1) * (107 + 2) / 6;
}

// REPEAT 8 - TIME: 10.3227785 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(108);
expect r0 == 108 * (108 + 1) * (108 + 2) / 6;
}

// REPEAT 9 - TIME: 10.9882267 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(109);
expect r0 == 109 * (109 + 1) * (109 + 2) / 6;
}

// REPEAT 10 - TIME: 11.5759006 s

// dafny-synthesis_task_id_80.dfy

method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
  requires n >= 0
  ensures t == n * (n + 1) * (n + 2) / 6
{
  t := n * (n + 1) * (n + 2) + 6;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(0);
expect r0 == 0 * (0 + 1) * (0 + 2) / 6;
}

// REPEAT 1 - TIME: 1.9617556 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(1);
expect r0 == 1 * (1 + 1) * (1 + 2) / 6;
}

// REPEAT 2 - TIME: 2.4903944 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(2);
expect r0 == 2 * (2 + 1) * (2 + 2) / 6;
}

// REPEAT 3 - TIME: 3.0193689 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(3);
expect r0 == 3 * (3 + 1) * (3 + 2) / 6;
}

// REPEAT 4 - TIME: 3.6145108 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(4);
expect r0 == 4 * (4 + 1) * (4 + 2) / 6;
}

// REPEAT 5 - TIME: 4.1831173 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(5);
expect r0 == 5 * (5 + 1) * (5 + 2) / 6;
}

// REPEAT 6 - TIME: 4.7468799 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(6);
expect r0 == 6 * (6 + 1) * (6 + 2) / 6;
}

// REPEAT 7 - TIME: 5.2740706 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(7);
expect r0 == 7 * (7 + 1) * (7 + 2) / 6;
}

// REPEAT 8 - TIME: 5.7855921 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(8);
expect r0 == 8 * (8 + 1) * (8 + 2) / 6;
}

// REPEAT 9 - TIME: 6.1883664 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(9);
expect r0 == 9 * (9 + 1) * (9 + 2) / 6;
}

// REPEAT 10 - TIME: 6.6694755 s

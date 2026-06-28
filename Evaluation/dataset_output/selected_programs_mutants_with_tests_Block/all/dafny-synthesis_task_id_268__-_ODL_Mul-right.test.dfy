// dafny-synthesis_task_id_268.dfy

method {:testEntry} StarNumber(n: int) returns (star: int)
  requires n >= 0
  ensures star == 6 * n * (n - 1) + 1
{
  star := 6 + 1;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(0);
expect r0 == 6 * 0 * (0 - 1) + 1;
}

// REPEAT 1 - TIME: 1.8934275 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(1);
expect r0 == 6 * 1 * (1 - 1) + 1;
}

// REPEAT 2 - TIME: 2.6468808 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(2);
expect r0 == 6 * 2 * (2 - 1) + 1;
}

// REPEAT 3 - TIME: 3.4636018 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(3);
expect r0 == 6 * 3 * (3 - 1) + 1;
}

// REPEAT 4 - TIME: 4.1927977 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(4);
expect r0 == 6 * 4 * (4 - 1) + 1;
}

// REPEAT 5 - TIME: 4.9995623 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(5);
expect r0 == 6 * 5 * (5 - 1) + 1;
}

// REPEAT 6 - TIME: 5.8131684 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(6);
expect r0 == 6 * 6 * (6 - 1) + 1;
}

// REPEAT 7 - TIME: 6.6572463 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(7);
expect r0 == 6 * 7 * (7 - 1) + 1;
}

// REPEAT 8 - TIME: 7.3449795 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(8);
expect r0 == 6 * 8 * (8 - 1) + 1;
}

// REPEAT 9 - TIME: 8.007604 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(9);
expect r0 == 6 * 9 * (9 - 1) + 1;
}

// REPEAT 10 - TIME: 8.5953643 s

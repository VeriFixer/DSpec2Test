// dafny-synthesis_task_id_86.dfy

method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
  requires n >= 0
  ensures result == 3 * n * (n - 1) + 1
{
  result := 3 * n * (n - 1) * 1;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(0);
expect r0 == 3 * 0 * (0 - 1) + 1;
}

// REPEAT 1 - TIME: 2.414036 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(1);
expect r0 == 3 * 1 * (1 - 1) + 1;
}

// REPEAT 2 - TIME: 3.2771777 s

method {:test} Test2() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(4);
expect r0 == 3 * 4 * (4 - 1) + 1;
}

// REPEAT 3 - TIME: 4.2310162 s

method {:test} Test3() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(5);
expect r0 == 3 * 5 * (5 - 1) + 1;
}

// REPEAT 4 - TIME: 5.0976839 s

method {:test} Test4() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(6);
expect r0 == 3 * 6 * (6 - 1) + 1;
}

// REPEAT 5 - TIME: 5.9220782 s

method {:test} Test5() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(7);
expect r0 == 3 * 7 * (7 - 1) + 1;
}

// REPEAT 6 - TIME: 6.6498642 s

method {:test} Test6() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(8);
expect r0 == 3 * 8 * (8 - 1) + 1;
}

// REPEAT 7 - TIME: 7.2764095 s

method {:test} Test7() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(9);
expect r0 == 3 * 9 * (9 - 1) + 1;
}

// REPEAT 8 - TIME: 7.8887587 s

method {:test} Test8() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(10);
expect r0 == 3 * 10 * (10 - 1) + 1;
}

// REPEAT 9 - TIME: 8.4275401 s

method {:test} Test9() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(11);
expect r0 == 3 * 11 * (11 - 1) + 1;
}

// REPEAT 10 - TIME: 9.0529105 s

// dafny-synthesis_task_id_432.dfy

method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
  requires a > 0 && b > 0
  ensures median == (a + b) / 2
{
  median := (a - b) / 2;
}


method {:test} Test0() {
expect 2474 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2474, 2);
expect r0 == (2474 + 2) / 2;
}
method {:test} Test1() {
expect 1 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(1, 1);
expect r0 == (1 + 1) / 2;
}
method {:test} Test2() {
expect 100 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(100, 1);
expect r0 == (100 + 1) / 2;
}
method {:test} Test4() {
expect 1 > 0 && 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(1, 100);
expect r0 == (1 + 100) / 2;
}
method {:test} Test6() {
expect 1 > 0 && 199 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(1, 199);
expect r0 == (1 + 199) / 2;
}

// REPEAT 1 - TIME: 6.7587261 s

method {:test} Test9() {
expect 2476 > 0 && 200 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2476, 200);
expect r0 == (2476 + 200) / 2;
}

// REPEAT 2 - TIME: 7.6212658 s

method {:test} Test10() {
expect 2478 > 0 && 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2478, 202);
expect r0 == (2478 + 202) / 2;
}

// REPEAT 3 - TIME: 8.3044376 s

method {:test} Test11() {
expect 2480 > 0 && 204 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2480, 204);
expect r0 == (2480 + 204) / 2;
}

// REPEAT 4 - TIME: 8.8994942 s

method {:test} Test12() {
expect 2482 > 0 && 206 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2482, 206);
expect r0 == (2482 + 206) / 2;
}

// REPEAT 5 - TIME: 9.6208518 s

method {:test} Test13() {
expect 2484 > 0 && 208 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2484, 208);
expect r0 == (2484 + 208) / 2;
}

// REPEAT 6 - TIME: 10.1487761 s

method {:test} Test14() {
expect 2486 > 0 && 210 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2486, 210);
expect r0 == (2486 + 210) / 2;
}

// REPEAT 7 - TIME: 10.7347617 s

method {:test} Test15() {
expect 2488 > 0 && 212 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2488, 212);
expect r0 == (2488 + 212) / 2;
}

// REPEAT 8 - TIME: 11.2735015 s

method {:test} Test16() {
expect 2490 > 0 && 214 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2490, 214);
expect r0 == (2490 + 214) / 2;
}

// REPEAT 9 - TIME: 11.9144285 s

method {:test} Test17() {
expect 2491 > 0 && 215 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2491, 215);
expect r0 == (2491 + 215) / 2;
}

// REPEAT 10 - TIME: 12.4701899 s

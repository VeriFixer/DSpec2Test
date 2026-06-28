// dafny-synthesis_task_id_432.dfy

method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
  requires a > 0 && b > 0
  ensures median == (a + b) / 2
{
  median := a / 2;
}


method {:test} Test0() {
expect 2 > 0 && 2474 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2, 2474);
expect r0 == (2 + 2474) / 2;
}

// REPEAT 1 - TIME: 2.0571479 s

method {:test} Test1() {
expect 3 > 0 && 2475 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(3, 2475);
expect r0 == (3 + 2475) / 2;
}

// REPEAT 2 - TIME: 2.8371845 s

method {:test} Test2() {
expect 4 > 0 && 2476 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(4, 2476);
expect r0 == (4 + 2476) / 2;
}

// REPEAT 3 - TIME: 3.5881416 s

method {:test} Test3() {
expect 5 > 0 && 2477 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(5, 2477);
expect r0 == (5 + 2477) / 2;
}

// REPEAT 4 - TIME: 4.3318468 s

method {:test} Test4() {
expect 6 > 0 && 2478 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(6, 2478);
expect r0 == (6 + 2478) / 2;
}

// REPEAT 5 - TIME: 5.127365 s

method {:test} Test5() {
expect 7 > 0 && 2479 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(7, 2479);
expect r0 == (7 + 2479) / 2;
}

// REPEAT 6 - TIME: 6.0243513 s

method {:test} Test6() {
expect 8 > 0 && 2480 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(8, 2480);
expect r0 == (8 + 2480) / 2;
}

// REPEAT 7 - TIME: 6.9714614 s

method {:test} Test7() {
expect 9 > 0 && 2481 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(9, 2481);
expect r0 == (9 + 2481) / 2;
}

// REPEAT 8 - TIME: 7.8160573 s

method {:test} Test8() {
expect 10 > 0 && 2482 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(10, 2482);
expect r0 == (10 + 2482) / 2;
}

// REPEAT 9 - TIME: 8.4907963 s

method {:test} Test9() {
expect 11 > 0 && 2483 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(11, 2483);
expect r0 == (11 + 2483) / 2;
}

// REPEAT 10 - TIME: 9.2242732 s

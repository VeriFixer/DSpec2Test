// dafny-synthesis_task_id_432.dfy

method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
  requires a > 0 && b > 0
  ensures median == (a + b) / 2
{
  median := (a + b) * 2;
}


method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test0() {
expect 2474 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2474, 2);
expect r0 == (2474 + 2) / 2;
}

// REPEAT 1 - TIME: 2.5620842 s

method {:test} Test1() {
expect 2476 > 0 && 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2476, 4);
expect r0 == (2476 + 4) / 2;
}

// REPEAT 2 - TIME: 3.6351904 s

method {:test} Test2() {
expect 2478 > 0 && 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2478, 6);
expect r0 == (2478 + 6) / 2;
}

// REPEAT 3 - TIME: 4.5977858 s

method {:test} Test3() {
expect 2480 > 0 && 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2480, 8);
expect r0 == (2480 + 8) / 2;
}

// REPEAT 4 - TIME: 5.6747051 s

method {:test} Test4() {
expect 2482 > 0 && 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2482, 10);
expect r0 == (2482 + 10) / 2;
}

// REPEAT 5 - TIME: 6.6765254 s

method {:test} Test5() {
expect 2484 > 0 && 12 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2484, 12);
expect r0 == (2484 + 12) / 2;
}

// REPEAT 6 - TIME: 7.5690202 s

method {:test} Test6() {
expect 2486 > 0 && 14 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2486, 14);
expect r0 == (2486 + 14) / 2;
}

// REPEAT 7 - TIME: 8.3906715 s

method {:test} Test7() {
expect 2488 > 0 && 16 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2488, 16);
expect r0 == (2488 + 16) / 2;
}

// REPEAT 8 - TIME: 8.9969033 s

method {:test} Test8() {
expect 2490 > 0 && 18 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2490, 18);
expect r0 == (2490 + 18) / 2;
}

// REPEAT 9 - TIME: 9.7471212 s

method {:test} Test9() {
expect 2492 > 0 && 20 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2492, 20);
expect r0 == (2492 + 20) / 2;
}

// REPEAT 10 - TIME: 10.3637075 s

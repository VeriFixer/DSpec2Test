// dafny-synthesis_task_id_266.dfy

method {:testEntry} LateralSurfaceArea(size: int) returns (area: int)
  requires size > 0
  ensures area == 4 * size * size
{
  area := 4 * size + size;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(1);
expect r0 == 4 * 1 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(100);
expect r0 == 4 * 100 * 100;
}

// REPEAT 1 - TIME: 5.1292988 s

method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(101);
expect r0 == 4 * 101 * 101;
}

// REPEAT 2 - TIME: 5.9695903 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(102);
expect r0 == 4 * 102 * 102;
}

// REPEAT 3 - TIME: 6.7907126 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(103);
expect r0 == 4 * 103 * 103;
}

// REPEAT 4 - TIME: 7.6739431 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(104);
expect r0 == 4 * 104 * 104;
}

// REPEAT 5 - TIME: 8.4481322 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(105);
expect r0 == 4 * 105 * 105;
}

// REPEAT 6 - TIME: 9.2372889 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(106);
expect r0 == 4 * 106 * 106;
}

// REPEAT 7 - TIME: 9.9394882 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(107);
expect r0 == 4 * 107 * 107;
}

// REPEAT 8 - TIME: 10.644402 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(108);
expect r0 == 4 * 108 * 108;
}

// REPEAT 9 - TIME: 11.2493614 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(109);
expect r0 == 4 * 109 * 109;
}

// REPEAT 10 - TIME: 11.906751 s

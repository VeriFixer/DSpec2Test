// dafny-synthesis_task_id_581.dfy

method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
  requires baseEdge > 0
  requires height > 0
  ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
  area := baseEdge * baseEdge;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 1);
expect r0 == 1 * 1 + 2 * 1 * 1;
}
method {:test} Test1() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 7720);
expect r0 == 1 * 1 + 2 * 1 * 7720;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(100, 1);
expect r0 == 100 * 100 + 2 * 100 * 1;
}
method {:test} Test4() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(1, 100);
expect r0 == 1 * 1 + 2 * 1 * 100;
}
method {:test} Test6() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 24 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(2, 24);
expect r0 == 2 * 2 + 2 * 2 * 24;
}

// REPEAT 1 - TIME: 6.7021167 s

method {:test} Test9() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(101, 7721);
expect r0 == 101 * 101 + 2 * 101 * 7721;
}

// REPEAT 2 - TIME: 7.5018332 s

method {:test} Test10() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(102, 7722);
expect r0 == 102 * 102 + 2 * 102 * 7722;
}

// REPEAT 3 - TIME: 8.2484997 s

method {:test} Test11() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(103, 7723);
expect r0 == 103 * 103 + 2 * 103 * 7723;
}

// REPEAT 4 - TIME: 9.0631134 s

method {:test} Test12() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(104, 7724);
expect r0 == 104 * 104 + 2 * 104 * 7724;
}

// REPEAT 5 - TIME: 9.6086567 s

method {:test} Test13() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(105, 7725);
expect r0 == 105 * 105 + 2 * 105 * 7725;
}

// REPEAT 6 - TIME: 10.4077151 s

method {:test} Test14() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(106, 7726);
expect r0 == 106 * 106 + 2 * 106 * 7726;
}

// REPEAT 7 - TIME: 10.9851539 s

method {:test} Test15() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(107, 7727);
expect r0 == 107 * 107 + 2 * 107 * 7727;
}

// REPEAT 8 - TIME: 11.5694514 s

method {:test} Test16() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(108, 7728);
expect r0 == 108 * 108 + 2 * 108 * 7728;
}

// REPEAT 9 - TIME: 12.2102922 s

method {:test} Test17() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(109, 7729);
expect r0 == 109 * 109 + 2 * 109 * 7729;
}

// REPEAT 10 - TIME: 12.750935 s

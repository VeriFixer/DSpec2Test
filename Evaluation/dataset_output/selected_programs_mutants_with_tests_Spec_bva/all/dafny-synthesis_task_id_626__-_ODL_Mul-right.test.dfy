// dafny-synthesis_task_id_626.dfy

method {:testEntry} AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
  requires radius > 0
  ensures area == radius * radius
{
  area := radius;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(1);
expect r0 == 1 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(100);
expect r0 == 100 * 100;
}
method {:test} Test4() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 8.2476588 s

method {:test} Test7() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 9.4411641 s

method {:test} Test8() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 10.3737604 s

method {:test} Test9() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 11.2949487 s

method {:test} Test10() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 12.2993251 s

method {:test} Test11() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 13.1064373 s

method {:test} Test12() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 13.953316 s

method {:test} Test13() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 14.6842525 s

method {:test} Test14() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 15.5888563 s

method {:test} Test15() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 16.5058622 s

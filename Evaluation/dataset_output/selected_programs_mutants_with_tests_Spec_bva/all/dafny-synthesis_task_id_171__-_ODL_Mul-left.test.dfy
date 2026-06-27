// dafny-synthesis_task_id_171.dfy

method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 5 * side
{
  perimeter := side;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(1);
expect r0 == 5 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(100);
expect r0 == 5 * 100;
}

// REPEAT 1 - TIME: 4.6391406 s

method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(101);
expect r0 == 5 * 101;
}

// REPEAT 2 - TIME: 5.5138982 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(102);
expect r0 == 5 * 102;
}

// REPEAT 3 - TIME: 6.5545116 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(103);
expect r0 == 5 * 103;
}

// REPEAT 4 - TIME: 7.3403383 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(104);
expect r0 == 5 * 104;
}

// REPEAT 5 - TIME: 8.3601082 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(105);
expect r0 == 5 * 105;
}

// REPEAT 6 - TIME: 9.1249746 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(106);
expect r0 == 5 * 106;
}

// REPEAT 7 - TIME: 10.009256 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(107);
expect r0 == 5 * 107;
}

// REPEAT 8 - TIME: 10.7045348 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(108);
expect r0 == 5 * 108;
}

// REPEAT 9 - TIME: 11.3348202 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(109);
expect r0 == 5 * 109;
}

// REPEAT 10 - TIME: 11.9768186 s

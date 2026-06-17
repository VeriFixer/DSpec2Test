// dafny-synthesis_task_id_171.dfy

method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 5 * side
{
  perimeter := -5 * side;
}


method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(1);
expect r0 == 5 * 1;
}

// REPEAT 1 - TIME: 4.4536726 s

method {:test} Test1() {
expect 40 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(40);
expect r0 == 5 * 40;
}

// REPEAT 2 - TIME: 5.8791525 s

method {:test} Test2() {
expect 41 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(41);
expect r0 == 5 * 41;
}

// REPEAT 3 - TIME: 7.5028572 s

method {:test} Test3() {
expect 42 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(42);
expect r0 == 5 * 42;
}

// REPEAT 4 - TIME: 8.9456226 s

method {:test} Test4() {
expect 43 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(43);
expect r0 == 5 * 43;
}

// REPEAT 5 - TIME: 10.3991106 s

method {:test} Test5() {
expect 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(44);
expect r0 == 5 * 44;
}

// REPEAT 6 - TIME: 11.4014907 s

method {:test} Test6() {
expect 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(45);
expect r0 == 5 * 45;
}

// REPEAT 7 - TIME: 12.4740832 s

method {:test} Test7() {
expect 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(46);
expect r0 == 5 * 46;
}

// REPEAT 8 - TIME: 13.5601293 s

method {:test} Test8() {
expect 47 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(47);
expect r0 == 5 * 47;
}

// REPEAT 9 - TIME: 14.7337675 s

method {:test} Test9() {
expect 48 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(48);
expect r0 == 5 * 48;
}

// REPEAT 10 - TIME: 16.0369127 s

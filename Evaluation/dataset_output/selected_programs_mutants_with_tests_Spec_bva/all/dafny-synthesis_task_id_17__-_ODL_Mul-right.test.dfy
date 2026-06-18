// dafny-synthesis_task_id_17.dfy

method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 4 * side
{
  perimeter := 4;
}


method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
{
    perimeter := 4 * side;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(1);
expect r0 == 4 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(100);
expect r0 == 4 * 100;
}

// REPEAT 1 - TIME: 4.6417947 s

method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(101);
expect r0 == 4 * 101;
}

// REPEAT 2 - TIME: 5.6035744 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(102);
expect r0 == 4 * 102;
}

// REPEAT 3 - TIME: 6.6966066 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(103);
expect r0 == 4 * 103;
}

// REPEAT 4 - TIME: 7.5506517 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(104);
expect r0 == 4 * 104;
}

// REPEAT 5 - TIME: 8.4088372 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(105);
expect r0 == 4 * 105;
}

// REPEAT 6 - TIME: 9.2317296 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(106);
expect r0 == 4 * 106;
}

// REPEAT 7 - TIME: 10.0175885 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(107);
expect r0 == 4 * 107;
}

// REPEAT 8 - TIME: 10.6663417 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(108);
expect r0 == 4 * 108;
}

// REPEAT 9 - TIME: 11.3055835 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(109);
expect r0 == 4 * 109;
}

// REPEAT 10 - TIME: 11.8104953 s

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

// REPEAT 1 - TIME: 4.6417428 s

method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(101);
expect r0 == 4 * 101;
}

// REPEAT 2 - TIME: 5.4968952 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(102);
expect r0 == 4 * 102;
}

// REPEAT 3 - TIME: 6.5283907 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(103);
expect r0 == 4 * 103;
}

// REPEAT 4 - TIME: 7.2738557 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(104);
expect r0 == 4 * 104;
}

// REPEAT 5 - TIME: 7.9427286 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(105);
expect r0 == 4 * 105;
}

// REPEAT 6 - TIME: 8.6646761 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(106);
expect r0 == 4 * 106;
}

// REPEAT 7 - TIME: 9.1956578 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(107);
expect r0 == 4 * 107;
}

// REPEAT 8 - TIME: 9.7552727 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(108);
expect r0 == 4 * 108;
}

// REPEAT 9 - TIME: 10.3625486 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(109);
expect r0 == 4 * 109;
}

// REPEAT 10 - TIME: 10.9764484 s

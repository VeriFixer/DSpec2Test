// dafny-synthesis_task_id_17.dfy

method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 4 * side
{
  perimeter := -4 * side;
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

// REPEAT 1 - TIME: 1.9900243 s

method {:test} Test1() {
expect 40 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(40);
expect r0 == 4 * 40;
}

// REPEAT 2 - TIME: 2.6515975 s

method {:test} Test2() {
expect 41 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(41);
expect r0 == 4 * 41;
}

// REPEAT 3 - TIME: 3.3809218 s

method {:test} Test3() {
expect 42 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(42);
expect r0 == 4 * 42;
}

// REPEAT 4 - TIME: 4.0544467 s

method {:test} Test4() {
expect 43 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(43);
expect r0 == 4 * 43;
}

// REPEAT 5 - TIME: 4.6911687 s

method {:test} Test5() {
expect 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(44);
expect r0 == 4 * 44;
}

// REPEAT 6 - TIME: 5.4870136 s

method {:test} Test6() {
expect 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(45);
expect r0 == 4 * 45;
}

// REPEAT 7 - TIME: 6.3069169 s

method {:test} Test7() {
expect 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(46);
expect r0 == 4 * 46;
}

// REPEAT 8 - TIME: 6.9901194 s

method {:test} Test8() {
expect 47 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(47);
expect r0 == 4 * 47;
}

// REPEAT 9 - TIME: 7.5662527 s

method {:test} Test9() {
expect 48 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(48);
expect r0 == 4 * 48;
}

// REPEAT 10 - TIME: 8.2263386 s

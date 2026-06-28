// dafny-synthesis_task_id_626.dfy

method {:testEntry} AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
  requires radius > 0
  ensures area == radius * radius
{
  area := radius + radius;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(1);
expect r0 == 1 * 1;
}

// REPEAT 1 - TIME: 2.3370908 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(2);
expect r0 == 2 * 2;
}

// REPEAT 2 - TIME: 3.103071 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 3.8796988 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(4);
expect r0 == 4 * 4;
}

// REPEAT 4 - TIME: 4.7361896 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(5);
expect r0 == 5 * 5;
}

// REPEAT 5 - TIME: 5.592393 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(6);
expect r0 == 6 * 6;
}

// REPEAT 6 - TIME: 6.271097 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(7);
expect r0 == 7 * 7;
}

// REPEAT 7 - TIME: 6.9057276 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(8);
expect r0 == 8 * 8;
}

// REPEAT 8 - TIME: 7.5278675 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(9);
expect r0 == 9 * 9;
}

// REPEAT 9 - TIME: 8.1513571 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(10);
expect r0 == 10 * 10;
}

// REPEAT 10 - TIME: 8.8484351 s

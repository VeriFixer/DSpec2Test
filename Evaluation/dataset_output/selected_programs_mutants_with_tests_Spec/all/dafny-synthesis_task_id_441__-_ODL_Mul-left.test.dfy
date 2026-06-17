// dafny-synthesis_task_id_441.dfy

method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
  requires size > 0
  ensures area == 6 * size * size
{
  area := size;
}


method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    area := 6 * size * size;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(1);
expect r0 == 6 * 1 * 1;
}

// REPEAT 1 - TIME: 2.5796417 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(2);
expect r0 == 6 * 2 * 2;
}

// REPEAT 2 - TIME: 3.50811 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(3);
expect r0 == 6 * 3 * 3;
}

// REPEAT 3 - TIME: 4.3888699 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(4);
expect r0 == 6 * 4 * 4;
}

// REPEAT 4 - TIME: 5.189869 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(5);
expect r0 == 6 * 5 * 5;
}

// REPEAT 5 - TIME: 5.998103 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(6);
expect r0 == 6 * 6 * 6;
}

// REPEAT 6 - TIME: 6.7370218 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(7);
expect r0 == 6 * 7 * 7;
}

// REPEAT 7 - TIME: 7.4531493 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(8);
expect r0 == 6 * 8 * 8;
}

// REPEAT 8 - TIME: 8.1832098 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(9);
expect r0 == 6 * 9 * 9;
}

// REPEAT 9 - TIME: 8.8149845 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(10);
expect r0 == 6 * 10 * 10;
}

// REPEAT 10 - TIME: 9.5838484 s

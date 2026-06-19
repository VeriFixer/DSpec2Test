// dafny-synthesis_task_id_85.dfy

method {:testEntry} SphereSurfaceArea(radius: real) returns (area: real)
  requires radius > 0.0
  ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
  area := -(4.0 * 3.14159265358979323846 * radius * radius);
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(1.0);
expect r0 == 4.0 * 3.14159265358979323846 * 1.0 * 1.0;
}

// REPEAT 1 - TIME: 2.5108121 s

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(2.0);
expect r0 == 4.0 * 3.14159265358979323846 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 3.332365 s

method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(3.0);
expect r0 == 4.0 * 3.14159265358979323846 * 3.0 * 3.0;
}

// REPEAT 3 - TIME: 4.2258017 s

method {:test} Test3() {
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(4.0);
expect r0 == 4.0 * 3.14159265358979323846 * 4.0 * 4.0;
}

// REPEAT 4 - TIME: 5.1365148 s

method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(5.0);
expect r0 == 4.0 * 3.14159265358979323846 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 5.9470041 s

method {:test} Test5() {
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(6.0);
expect r0 == 4.0 * 3.14159265358979323846 * 6.0 * 6.0;
}

// REPEAT 6 - TIME: 6.8042738 s

method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(7.0);
expect r0 == 4.0 * 3.14159265358979323846 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 7.6204171 s

method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(8.0);
expect r0 == 4.0 * 3.14159265358979323846 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 8.1813459 s

method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(9.0);
expect r0 == 4.0 * 3.14159265358979323846 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 8.9462482 s

method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(10.0);
expect r0 == 4.0 * 3.14159265358979323846 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 9.5734474 s

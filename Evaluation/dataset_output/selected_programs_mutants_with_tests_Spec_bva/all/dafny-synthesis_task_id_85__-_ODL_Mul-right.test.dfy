// dafny-synthesis_task_id_85.dfy

method {:testEntry} SphereSurfaceArea(radius: real) returns (area: real)
  requires radius > 0.0
  ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
  area := 4.0;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(1.0);
expect r0 == 4.0 * 3.14159265358979323846 * 1.0 * 1.0;
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(1.0/10000.0);
expect r0 == 4.0 * 3.14159265358979323846 * 1.0/10000.0 * 1.0/10000.0;
}
method {:test} Test2() {
expect 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(100.0);
expect r0 == 4.0 * 3.14159265358979323846 * 100.0 * 100.0;
}

// REPEAT 1 - TIME: 5.2769875 s

method {:test} Test6() {
expect 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(101.0);
expect r0 == 4.0 * 3.14159265358979323846 * 101.0 * 101.0;
}

// REPEAT 2 - TIME: 6.3015885 s

method {:test} Test7() {
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(102.0);
expect r0 == 4.0 * 3.14159265358979323846 * 102.0 * 102.0;
}

// REPEAT 3 - TIME: 7.1857237 s

method {:test} Test8() {
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(103.0);
expect r0 == 4.0 * 3.14159265358979323846 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 8.0498442 s

method {:test} Test9() {
expect 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(104.0);
expect r0 == 4.0 * 3.14159265358979323846 * 104.0 * 104.0;
}

// REPEAT 5 - TIME: 8.7691827 s

method {:test} Test10() {
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(105.0);
expect r0 == 4.0 * 3.14159265358979323846 * 105.0 * 105.0;
}

// REPEAT 6 - TIME: 9.4958407 s

method {:test} Test11() {
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(106.0);
expect r0 == 4.0 * 3.14159265358979323846 * 106.0 * 106.0;
}

// REPEAT 7 - TIME: 10.1281223 s

method {:test} Test12() {
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(107.0);
expect r0 == 4.0 * 3.14159265358979323846 * 107.0 * 107.0;
}

// REPEAT 8 - TIME: 10.6553509 s

method {:test} Test13() {
expect 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(108.0);
expect r0 == 4.0 * 3.14159265358979323846 * 108.0 * 108.0;
}

// REPEAT 9 - TIME: 11.1691313 s

method {:test} Test14() {
expect 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(109.0);
expect r0 == 4.0 * 3.14159265358979323846 * 109.0 * 109.0;
}

// REPEAT 10 - TIME: 11.746468 s

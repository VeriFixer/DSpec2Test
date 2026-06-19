// dafny-synthesis_task_id_82.dfy

method {:testEntry} SphereVolume(radius: real) returns (volume: real)
  requires radius > 0.0
  ensures volume == 4.0 / 3.0 * 3.1415926535 * radius * radius * radius
{
  volume := (4.0 / 3.0 * 3.1415926535 * radius - radius) * radius;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(1.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 1.0 * 1.0 * 1.0;
}

// REPEAT 1 - TIME: 1.4105088 s

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(2.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 2.0 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 1.8714382 s

method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(3.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 3.0 * 3.0 * 3.0;
}

// REPEAT 3 - TIME: 2.3923731 s

method {:test} Test3() {
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(4.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 4.0 * 4.0 * 4.0;
}

// REPEAT 4 - TIME: 3.0019159 s

method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(5.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 5.0 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 3.5312339 s

method {:test} Test5() {
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(6.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 6.0 * 6.0 * 6.0;
}

// REPEAT 6 - TIME: 4.0763654 s

method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(7.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 4.6307097 s

method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(8.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 8.0 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 5.1851112 s

method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(9.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 5.7358267 s

method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(10.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 10.0 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 6.3299048 s

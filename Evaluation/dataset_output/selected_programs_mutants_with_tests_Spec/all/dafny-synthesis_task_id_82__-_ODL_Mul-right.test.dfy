// dafny-synthesis_task_id_82.dfy

method {:testEntry} SphereVolume(radius: real) returns (volume: real)
  requires radius > 0.0
  ensures volume == 4.0 / 3.0 * 3.1415926535 * radius * radius * radius
{
  volume := 4.0 / 3.0;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(1.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 1.0 * 1.0 * 1.0;
}

// REPEAT 1 - TIME: 2.6191912 s

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(2.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 2.0 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 3.3980903 s

method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(3.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 3.0 * 3.0 * 3.0;
}

// REPEAT 3 - TIME: 4.2388991 s

method {:test} Test3() {
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(4.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 4.0 * 4.0 * 4.0;
}

// REPEAT 4 - TIME: 5.1316691 s

method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(5.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 5.0 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 6.0871755 s

method {:test} Test5() {
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(6.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 6.0 * 6.0 * 6.0;
}

// REPEAT 6 - TIME: 7.0127685 s

method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(7.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 7.9745008 s

method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(8.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 8.0 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 8.8699671 s

method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(9.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 9.6187571 s

method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(10.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 10.0 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 10.2716419 s

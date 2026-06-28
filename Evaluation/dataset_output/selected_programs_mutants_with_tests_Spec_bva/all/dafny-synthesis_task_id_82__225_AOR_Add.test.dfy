// dafny-synthesis_task_id_82.dfy

method {:testEntry} SphereVolume(radius: real) returns (volume: real)
  requires radius > 0.0
  ensures volume == 4.0 / 3.0 * 3.1415926535 * radius * radius * radius
{
  volume := 4.0 / 3.0 * 3.1415926535 * radius * radius + radius;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(1.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 1.0 * 1.0 * 1.0;
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(1.0/10000.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 1.0/10000.0 * 1.0/10000.0 * 1.0/10000.0;
}
method {:test} Test2() {
expect 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(100.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 100.0 * 100.0 * 100.0;
}

// REPEAT 1 - TIME: 6.1292266 s

method {:test} Test6() {
expect 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(101.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 101.0 * 101.0 * 101.0;
}

// REPEAT 2 - TIME: 7.3564141 s

method {:test} Test7() {
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(102.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 102.0 * 102.0 * 102.0;
}

// REPEAT 3 - TIME: 8.528673 s

method {:test} Test8() {
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(103.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 103.0 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 9.6991258 s

method {:test} Test9() {
expect 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(104.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 104.0 * 104.0 * 104.0;
}

// REPEAT 5 - TIME: 10.6706514 s

method {:test} Test10() {
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(105.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 105.0 * 105.0 * 105.0;
}

// REPEAT 6 - TIME: 11.5249334 s

method {:test} Test11() {
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(106.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 106.0 * 106.0 * 106.0;
}

// REPEAT 7 - TIME: 12.2820063 s

method {:test} Test12() {
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(107.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 107.0 * 107.0 * 107.0;
}

// REPEAT 8 - TIME: 13.0621512 s

method {:test} Test13() {
expect 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(108.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 108.0 * 108.0 * 108.0;
}

// REPEAT 9 - TIME: 13.7556093 s

method {:test} Test14() {
expect 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(109.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 109.0 * 109.0 * 109.0;
}

// REPEAT 10 - TIME: 14.377926 s

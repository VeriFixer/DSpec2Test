// dafny-synthesis_task_id_312.dfy

method {:testEntry} ConeVolume(radius: real, height: real) returns (volume: real)
  requires radius > 0.0 && height > 0.0
  ensures volume == 1.0 / 3.0 * 3.14159265358979323846 * radius * radius * height
{
  volume := height;
}


method {:test} Test0() {
expect 1.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(1.0, 1.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 1.0 * 1.0 * 1.0;
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(1.0/10000.0, 1.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 1.0/10000.0 * 1.0/10000.0 * 1.0;
}
method {:test} Test2() {
expect 100.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(100.0, 1.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 100.0 * 100.0 * 1.0;
}
method {:test} Test3() {
expect 1.0 > 0.0 && 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(1.0, 1.0/10000.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 1.0 * 1.0 * 1.0/10000.0;
}
method {:test} Test4() {
expect 1.0 > 0.0 && 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(1.0, 100.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 1.0 * 1.0 * 100.0;
}

// REPEAT 1 - TIME: 7.6369065 s

method {:test} Test8() {
expect 101.0 > 0.0 && 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(101.0, 101.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 101.0 * 101.0 * 101.0;
}

// REPEAT 2 - TIME: 8.8753469 s

method {:test} Test9() {
expect 102.0 > 0.0 && 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(102.0, 102.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 102.0 * 102.0 * 102.0;
}

// REPEAT 3 - TIME: 10.0621983 s

method {:test} Test10() {
expect 103.0 > 0.0 && 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(103.0, 103.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 103.0 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 11.0694323 s

method {:test} Test11() {
expect 104.0 > 0.0 && 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(104.0, 104.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 104.0 * 104.0 * 104.0;
}

// REPEAT 5 - TIME: 11.9365275 s

method {:test} Test12() {
expect 105.0 > 0.0 && 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(105.0, 105.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 105.0 * 105.0 * 105.0;
}

// REPEAT 6 - TIME: 12.683865 s

method {:test} Test13() {
expect 106.0 > 0.0 && 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(106.0, 106.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 106.0 * 106.0 * 106.0;
}

// REPEAT 7 - TIME: 13.4537481 s

method {:test} Test14() {
expect 107.0 > 0.0 && 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(107.0, 107.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 107.0 * 107.0 * 107.0;
}

// REPEAT 8 - TIME: 14.2329959 s

method {:test} Test15() {
expect 108.0 > 0.0 && 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(108.0, 108.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 108.0 * 108.0 * 108.0;
}

// REPEAT 9 - TIME: 14.9616156 s

method {:test} Test16() {
expect 109.0 > 0.0 && 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(109.0, 109.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 109.0 * 109.0 * 109.0;
}

// REPEAT 10 - TIME: 15.5837765 s

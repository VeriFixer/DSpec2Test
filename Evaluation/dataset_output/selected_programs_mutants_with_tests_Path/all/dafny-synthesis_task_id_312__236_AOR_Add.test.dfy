// dafny-synthesis_task_id_312.dfy

method {:testEntry} ConeVolume(radius: real, height: real) returns (volume: real)
  requires radius > 0.0 && height > 0.0
  ensures volume == 1.0 / 3.0 * 3.14159265358979323846 * radius * radius * height
{
  volume := (1.0 / 3.0 + 3.14159265358979323846) * radius * radius * height;
}


method {:test} Test0() {
expect 1.0 > 0.0 && 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(1.0, 1.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 1.0 * 1.0 * 1.0;
}

// REPEAT 1 - TIME: 2.9526416 s

method {:test} Test1() {
expect 2.0 > 0.0 && 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(2.0, 2.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 2.0 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 3.9132644 s

method {:test} Test2() {
expect 3.0 > 0.0 && 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(3.0, 3.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 3.0 * 3.0 * 3.0;
}

// REPEAT 3 - TIME: 4.9771305 s

method {:test} Test3() {
expect 4.0 > 0.0 && 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(4.0, 4.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 4.0 * 4.0 * 4.0;
}

// REPEAT 4 - TIME: 6.0906495 s

method {:test} Test4() {
expect 5.0 > 0.0 && 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(5.0, 5.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 5.0 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 7.114294 s

method {:test} Test5() {
expect 6.0 > 0.0 && 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(6.0, 6.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 6.0 * 6.0 * 6.0;
}

// REPEAT 6 - TIME: 7.929178 s

method {:test} Test6() {
expect 7.0 > 0.0 && 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(7.0, 7.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 8.6746435 s

method {:test} Test7() {
expect 8.0 > 0.0 && 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(8.0, 8.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 8.0 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 9.548294 s

method {:test} Test8() {
expect 9.0 > 0.0 && 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(9.0, 9.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 10.1935683 s

method {:test} Test9() {
expect 10.0 > 0.0 && 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(10.0, 10.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 10.0 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 10.9563824 s

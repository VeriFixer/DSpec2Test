// dafny-synthesis_task_id_276.dfy

method {:testEntry} CylinderVolume(radius: real, height: real) returns (volume: real)
  requires radius > 0.0
  requires height > 0.0
  ensures volume == 3.14159265359 * radius * radius * height
{
  volume := (3.14159265359 + radius) * radius * height;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(1.0, 1.0);
expect r0 == 3.14159265359 * 1.0 * 1.0 * 1.0;
}

// REPEAT 1 - TIME: 2.6529379 s

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(2.0, 2.0);
expect r0 == 3.14159265359 * 2.0 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 3.6632841 s

method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(3.0, 3.0);
expect r0 == 3.14159265359 * 3.0 * 3.0 * 3.0;
}

// REPEAT 3 - TIME: 4.6958922 s

method {:test} Test3() {
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(4.0, 4.0);
expect r0 == 3.14159265359 * 4.0 * 4.0 * 4.0;
}

// REPEAT 4 - TIME: 5.7701186 s

method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(5.0, 5.0);
expect r0 == 3.14159265359 * 5.0 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 6.9210288 s

method {:test} Test5() {
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(6.0, 6.0);
expect r0 == 3.14159265359 * 6.0 * 6.0 * 6.0;
}

// REPEAT 6 - TIME: 8.0175115 s

method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(7.0, 7.0);
expect r0 == 3.14159265359 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 8.7814918 s

method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(8.0, 8.0);
expect r0 == 3.14159265359 * 8.0 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 9.5263311 s

method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(9.0, 9.0);
expect r0 == 3.14159265359 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 10.2691028 s

method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(10.0, 10.0);
expect r0 == 3.14159265359 * 10.0 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 11.0481384 s

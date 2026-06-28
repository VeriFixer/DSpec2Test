// dafny-synthesis_task_id_276.dfy

method {:testEntry} CylinderVolume(radius: real, height: real) returns (volume: real)
  requires radius > 0.0
  requires height > 0.0
  ensures volume == 3.14159265359 * radius * radius * height
{
  volume := 3.14159265359 * radius * radius - height;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(1.0, 1.0);
expect r0 == 3.14159265359 * 1.0 * 1.0 * 1.0;
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(1.0/10000.0, 1.0);
expect r0 == 3.14159265359 * 1.0/10000.0 * 1.0/10000.0 * 1.0;
}
method {:test} Test2() {
expect 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(100.0, 1.0);
expect r0 == 3.14159265359 * 100.0 * 100.0 * 1.0;
}
method {:test} Test3() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(1.0, 1.0/10000.0);
expect r0 == 3.14159265359 * 1.0 * 1.0 * 1.0/10000.0;
}
method {:test} Test4() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(1.0, 100.0);
expect r0 == 3.14159265359 * 1.0 * 1.0 * 100.0;
}

// REPEAT 1 - TIME: 7.7451055 s

method {:test} Test8() {
expect 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(101.0, 101.0);
expect r0 == 3.14159265359 * 101.0 * 101.0 * 101.0;
}

// REPEAT 2 - TIME: 8.8532501 s

method {:test} Test9() {
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(102.0, 102.0);
expect r0 == 3.14159265359 * 102.0 * 102.0 * 102.0;
}

// REPEAT 3 - TIME: 9.8941584 s

method {:test} Test10() {
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(103.0, 103.0);
expect r0 == 3.14159265359 * 103.0 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 10.8925994 s

method {:test} Test11() {
expect 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(104.0, 104.0);
expect r0 == 3.14159265359 * 104.0 * 104.0 * 104.0;
}

// REPEAT 5 - TIME: 11.9267866 s

method {:test} Test12() {
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(105.0, 105.0);
expect r0 == 3.14159265359 * 105.0 * 105.0 * 105.0;
}

// REPEAT 6 - TIME: 12.843297 s

method {:test} Test13() {
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(106.0, 106.0);
expect r0 == 3.14159265359 * 106.0 * 106.0 * 106.0;
}

// REPEAT 7 - TIME: 13.799687 s

method {:test} Test14() {
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(107.0, 107.0);
expect r0 == 3.14159265359 * 107.0 * 107.0 * 107.0;
}

// REPEAT 8 - TIME: 14.8403683 s

method {:test} Test15() {
expect 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(108.0, 108.0);
expect r0 == 3.14159265359 * 108.0 * 108.0 * 108.0;
}

// REPEAT 9 - TIME: 15.9020562 s

method {:test} Test16() {
expect 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(109.0, 109.0);
expect r0 == 3.14159265359 * 109.0 * 109.0 * 109.0;
}

// REPEAT 10 - TIME: 16.924023 s

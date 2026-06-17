// dafny-synthesis_task_id_276.dfy

method {:testEntry} CylinderVolume(radius: real, height: real) returns (volume: real)
  requires radius > 0.0
  requires height > 0.0
  ensures volume == 3.14159265359 * radius * radius * height
{
  volume := 0.0;
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

// REPEAT 1 - TIME: 5.4201875 s

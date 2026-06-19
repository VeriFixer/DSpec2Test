// dafny-synthesis_task_id_312.dfy

method {:testEntry} ConeVolume(radius: real, height: real) returns (volume: real)
  requires radius > 0.0 && height > 0.0
  ensures volume == 1.0 / 3.0 * 3.14159265358979323846 * radius * radius * height
{
  volume := (1.0 / 3.0 * 3.14159265358979323846 + radius) * radius * height;
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

// REPEAT 1 - TIME: 6.5716305 s

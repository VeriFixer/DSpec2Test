// dafny-synthesis_task_id_139.dfy

method {:testEntry} CircleCircumference(radius: real) returns (circumference: real)
  requires radius > 0.0
  ensures circumference == 2.0 * 3.14159265358979323846 * radius
{
  circumference := (2.0 + 3.14159265358979323846) * radius;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(1.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0;
}

// REPEAT 1 - TIME: 1.8573285 s

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(2.0);
expect r0 == 2.0 * 3.14159265358979323846 * 2.0;
}

// REPEAT 2 - TIME: 2.5469089 s

method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(3.0);
expect r0 == 2.0 * 3.14159265358979323846 * 3.0;
}

// REPEAT 3 - TIME: 3.2473002 s

method {:test} Test3() {
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(4.0);
expect r0 == 2.0 * 3.14159265358979323846 * 4.0;
}

// REPEAT 4 - TIME: 3.921822 s

method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(5.0);
expect r0 == 2.0 * 3.14159265358979323846 * 5.0;
}

// REPEAT 5 - TIME: 4.9424661 s

method {:test} Test5() {
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(6.0);
expect r0 == 2.0 * 3.14159265358979323846 * 6.0;
}

// REPEAT 6 - TIME: 5.7939794 s

method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(7.0);
expect r0 == 2.0 * 3.14159265358979323846 * 7.0;
}

// REPEAT 7 - TIME: 6.6725725 s

method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(8.0);
expect r0 == 2.0 * 3.14159265358979323846 * 8.0;
}

// REPEAT 8 - TIME: 7.5456231 s

method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(9.0);
expect r0 == 2.0 * 3.14159265358979323846 * 9.0;
}

// REPEAT 9 - TIME: 8.241694 s

method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(10.0);
expect r0 == 2.0 * 3.14159265358979323846 * 10.0;
}

// REPEAT 10 - TIME: 8.9007135 s

// dafny-synthesis_task_id_139.dfy

method {:testEntry} CircleCircumference(radius: real) returns (circumference: real)
  requires radius > 0.0
  ensures circumference == 2.0 * 3.14159265358979323846 * radius
{
  circumference := 0.0 * radius;
}


method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(1.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0;
}

// REPEAT 1 - TIME: 2.5169301 s

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(2.0);
expect r0 == 2.0 * 3.14159265358979323846 * 2.0;
}

// REPEAT 2 - TIME: 3.5795328 s

method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(3.0);
expect r0 == 2.0 * 3.14159265358979323846 * 3.0;
}

// REPEAT 3 - TIME: 4.7078645 s

method {:test} Test3() {
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(4.0);
expect r0 == 2.0 * 3.14159265358979323846 * 4.0;
}

// REPEAT 4 - TIME: 5.7629425 s

method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(5.0);
expect r0 == 2.0 * 3.14159265358979323846 * 5.0;
}

// REPEAT 5 - TIME: 6.8250299 s

method {:test} Test5() {
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(6.0);
expect r0 == 2.0 * 3.14159265358979323846 * 6.0;
}

// REPEAT 6 - TIME: 7.6115988 s

method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(7.0);
expect r0 == 2.0 * 3.14159265358979323846 * 7.0;
}

// REPEAT 7 - TIME: 8.3830882 s

method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(8.0);
expect r0 == 2.0 * 3.14159265358979323846 * 8.0;
}

// REPEAT 8 - TIME: 9.0318962 s

method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(9.0);
expect r0 == 2.0 * 3.14159265358979323846 * 9.0;
}

// REPEAT 9 - TIME: 9.7015366 s

method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(10.0);
expect r0 == 2.0 * 3.14159265358979323846 * 10.0;
}

// REPEAT 10 - TIME: 10.3548132 s

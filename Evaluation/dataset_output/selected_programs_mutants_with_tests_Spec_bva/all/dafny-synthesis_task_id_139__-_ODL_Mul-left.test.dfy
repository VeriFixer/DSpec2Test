// dafny-synthesis_task_id_139.dfy

method {:testEntry} CircleCircumference(radius: real) returns (circumference: real)
  requires radius > 0.0
  ensures circumference == 2.0 * 3.14159265358979323846 * radius
{
  circumference := radius;
}


method {:testEntry} CircleCircumference(radius: real) returns (circumference: real)
    requires radius > 0.0
    ensures circumference == 2.0 * 3.14159265358979323846 * radius
{
    circumference := 2.0 * 3.14159265358979323846 * radius;
}

method {:test} Test0() {
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(1.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0;
}
method {:test} Test1() {
expect 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(1.0/10000.0);
expect r0 == 2.0 * 3.14159265358979323846 * 1.0/10000.0;
}
method {:test} Test2() {
expect 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(100.0);
expect r0 == 2.0 * 3.14159265358979323846 * 100.0;
}

// REPEAT 1 - TIME: 4.8936117 s

method {:test} Test6() {
expect 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(101.0);
expect r0 == 2.0 * 3.14159265358979323846 * 101.0;
}

// REPEAT 2 - TIME: 5.9045331 s

method {:test} Test7() {
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(102.0);
expect r0 == 2.0 * 3.14159265358979323846 * 102.0;
}

// REPEAT 3 - TIME: 6.9598613 s

method {:test} Test8() {
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(103.0);
expect r0 == 2.0 * 3.14159265358979323846 * 103.0;
}

// REPEAT 4 - TIME: 7.7846596 s

method {:test} Test9() {
expect 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(104.0);
expect r0 == 2.0 * 3.14159265358979323846 * 104.0;
}

// REPEAT 5 - TIME: 8.4471797 s

method {:test} Test10() {
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(105.0);
expect r0 == 2.0 * 3.14159265358979323846 * 105.0;
}

// REPEAT 6 - TIME: 9.1130198 s

method {:test} Test11() {
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(106.0);
expect r0 == 2.0 * 3.14159265358979323846 * 106.0;
}

// REPEAT 7 - TIME: 9.6755839 s

method {:test} Test12() {
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(107.0);
expect r0 == 2.0 * 3.14159265358979323846 * 107.0;
}

// REPEAT 8 - TIME: 10.3934646 s

method {:test} Test13() {
expect 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(108.0);
expect r0 == 2.0 * 3.14159265358979323846 * 108.0;
}

// REPEAT 9 - TIME: 10.9871461 s

method {:test} Test14() {
expect 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(109.0);
expect r0 == 2.0 * 3.14159265358979323846 * 109.0;
}

// REPEAT 10 - TIME: 11.6753875 s

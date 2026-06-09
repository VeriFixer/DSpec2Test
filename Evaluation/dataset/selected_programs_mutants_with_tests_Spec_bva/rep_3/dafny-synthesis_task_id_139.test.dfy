
method {:test} Test7() {
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(102.0);
expect r0 == 2.0 * 3.14159265358979323846 * 102.0;
}

// REPEAT 3 - TIME: 6.5030864 s
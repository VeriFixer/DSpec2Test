method {:testEntry} CircleCircumference(radius: real) returns (circumference: real)
    requires radius > 0.0
    ensures circumference == 2.0 * 3.14159265358979323846 * radius
{
    circumference := 2.0 * 3.14159265358979323846 * radius;
}

method {:test} Test13() {
expect 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(108.0);
expect r0 == 2.0 * 3.14159265358979323846 * 108.0;
}

// REPEAT 9 - TIME: 12.5564109 s

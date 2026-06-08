method {:testEntry} CircleCircumference(radius: real) returns (circumference: real)
    requires radius > 0.0
    ensures circumference == 2.0 * 3.14159265358979323846 * radius
{
    circumference := 2.0 * 3.14159265358979323846 * radius;
}

method {:test} Test12() {
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CircleCircumference(107.0);
expect r0 == 2.0 * 3.14159265358979323846 * 107.0;
}

// REPEAT 8 - TIME: 11.8501348 s

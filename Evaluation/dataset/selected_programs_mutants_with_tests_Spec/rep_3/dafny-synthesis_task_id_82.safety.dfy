method {:testEntry} SphereVolume(radius: real) returns (volume: real)
    requires radius > 0.0
    ensures volume == 4.0/3.0 * 3.1415926535 * radius * radius * radius
{
    volume := 4.0/3.0 * 3.1415926535 * radius * radius * radius;
}

method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(3.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 3.0 * 3.0 * 3.0;
}

// REPEAT 3 - TIME: 4.2754405 s

method {:testEntry} SphereVolume(radius: real) returns (volume: real)
    requires radius > 0.0
    ensures volume == 4.0/3.0 * 3.1415926535 * radius * radius * radius
{
    volume := 4.0/3.0 * 3.1415926535 * radius * radius * radius;
}

method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(2.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 2.0 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 3.5797366 s

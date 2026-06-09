method {:testEntry} ConeVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0 && height > 0.0
    ensures volume == (1.0/3.0) * (3.14159265358979323846) * radius * radius * height
{
    volume := (1.0/3.0) * (3.14159265358979323846) * radius * radius * height;
}

method {:test} Test6() {
expect 7.0 > 0.0 && 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(7.0, 7.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 6.4421297 s

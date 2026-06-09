method {:testEntry} ConeVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0 && height > 0.0
    ensures volume == (1.0/3.0) * (3.14159265358979323846) * radius * radius * height
{
    volume := (1.0/3.0) * (3.14159265358979323846) * radius * radius * height;
}

method {:test} Test8() {
expect 9.0 > 0.0 && 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(9.0, 9.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 7.5625323 s

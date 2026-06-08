method {:testEntry} ConeVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0 && height > 0.0
    ensures volume == (1.0/3.0) * (3.14159265358979323846) * radius * radius * height
{
    volume := (1.0/3.0) * (3.14159265358979323846) * radius * radius * height;
}

method {:test} Test9() {
expect 10.0 > 0.0 && 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(10.0, 10.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 10.0 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 9.4102482 s

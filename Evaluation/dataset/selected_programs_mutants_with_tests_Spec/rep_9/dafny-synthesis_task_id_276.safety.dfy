method {:testEntry} CylinderVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0
    requires height > 0.0
    ensures volume == 3.14159265359 * radius * radius * height
{
    volume := 3.14159265359 * radius * radius * height;
}

method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(9.0, 9.0);
expect r0 == 3.14159265359 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 8.901758 s

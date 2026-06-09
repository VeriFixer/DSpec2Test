method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test5() {
var r0 := DegreesToRadians(5.0);
expect r0 == 5.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 6 - TIME: 6.6801043 s

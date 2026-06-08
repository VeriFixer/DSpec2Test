method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test9() {
var r0 := DegreesToRadians(9.0);
expect r0 == 9.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 10 - TIME: 9.7558147 s

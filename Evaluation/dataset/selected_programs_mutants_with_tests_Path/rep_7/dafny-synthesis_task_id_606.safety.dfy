method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test6() {
var r0 := DegreesToRadians(6.0);
expect r0 == 6.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 7 - TIME: 9.5744337 s

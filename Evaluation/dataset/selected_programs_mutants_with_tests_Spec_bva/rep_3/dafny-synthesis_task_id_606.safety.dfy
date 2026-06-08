method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test9() {
var r0 := DegreesToRadians(900314159265358979323846.0/157079632679489661923.0);
expect r0 == 900314159265358979323846.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 3 - TIME: 7.5994451 s

method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test15() {
var r0 := DegreesToRadians(901256637061435917295384.0/157079632679489661923.0);
expect r0 == 901256637061435917295384.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 9 - TIME: 12.0197663 s

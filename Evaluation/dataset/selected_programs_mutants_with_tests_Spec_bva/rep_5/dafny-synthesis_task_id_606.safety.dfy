method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test11() {
var r0 := DegreesToRadians(900628318530717958647692.0/157079632679489661923.0);
expect r0 == 900628318530717958647692.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 5 - TIME: 8.516086 s

method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test13() {
var r0 := DegreesToRadians(900942477796076937971538.0/157079632679489661923.0);
expect r0 == 900942477796076937971538.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 7 - TIME: 9.924519 s

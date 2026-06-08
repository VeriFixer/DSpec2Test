method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test12() {
var r0 := DegreesToRadians(900785398163397448309615.0/157079632679489661923.0);
expect r0 == 900785398163397448309615.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 6 - TIME: 9.7812105 s

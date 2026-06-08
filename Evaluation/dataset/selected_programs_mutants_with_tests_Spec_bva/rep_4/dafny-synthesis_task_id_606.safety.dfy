method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    radians := degrees * 3.14159265358979323846 / 180.0;
}

method {:test} Test10() {
var r0 := DegreesToRadians(900471238898038468985769.0/157079632679489661923.0);
expect r0 == 900471238898038468985769.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 4 - TIME: 8.2822638 s

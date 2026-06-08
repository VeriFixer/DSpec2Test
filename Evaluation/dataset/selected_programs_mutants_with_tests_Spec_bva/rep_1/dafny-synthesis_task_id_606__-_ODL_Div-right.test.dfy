// dafny-synthesis_task_id_606.dfy

method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
  ensures radians == degrees * 3.14159265358979323846 / 180.0
{
  radians := degrees * 3.14159265358979323846;
}

method {:test} Test0() {
var r0 := DegreesToRadians(0.0);
expect r0 == 0.0 * 3.14159265358979323846 / 180.0;
}
method {:test} Test1() {
var r0 := DegreesToRadians(-100.0);
expect r0 == -100.0 * 3.14159265358979323846 / 180.0;
}
method {:test} Test2() {
var r0 := DegreesToRadians(100.0);
expect r0 == 100.0 * 3.14159265358979323846 / 180.0;
}
method {:test} Test4() {
var r0 := DegreesToRadians(-900000000000000000000000.0/157079632679489661923.0);
expect r0 == -900000000000000000000000.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}
method {:test} Test5() {
var r0 := DegreesToRadians(900000000000000000000000.0/157079632679489661923.0);
expect r0 == 900000000000000000000000.0/157079632679489661923.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 1 - TIME: 5.8933697 s

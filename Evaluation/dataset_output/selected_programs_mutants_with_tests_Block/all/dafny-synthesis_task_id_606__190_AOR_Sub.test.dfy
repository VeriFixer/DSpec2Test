// dafny-synthesis_task_id_606.dfy

method {:testEntry} DegreesToRadians(degrees: real) returns (radians: real)
  ensures radians == degrees * 3.14159265358979323846 / 180.0
{
  radians := degrees * 3.14159265358979323846 - 180.0;
}


method {:test} Test0() {
var r0 := DegreesToRadians(0.0);
expect r0 == 0.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 1 - TIME: 2.2378232 s

method {:test} Test1() {
var r0 := DegreesToRadians(1.0);
expect r0 == 1.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 2 - TIME: 2.9475655 s

method {:test} Test2() {
var r0 := DegreesToRadians(2.0);
expect r0 == 2.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 3 - TIME: 3.6884891 s

method {:test} Test3() {
var r0 := DegreesToRadians(3.0);
expect r0 == 3.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 4 - TIME: 4.3887323 s

method {:test} Test4() {
var r0 := DegreesToRadians(4.0);
expect r0 == 4.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 5 - TIME: 5.064983 s

method {:test} Test5() {
var r0 := DegreesToRadians(5.0);
expect r0 == 5.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 6 - TIME: 5.7684182 s

method {:test} Test6() {
var r0 := DegreesToRadians(6.0);
expect r0 == 6.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 7 - TIME: 6.3534951 s

method {:test} Test7() {
var r0 := DegreesToRadians(7.0);
expect r0 == 7.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 8 - TIME: 7.0004925 s

method {:test} Test8() {
var r0 := DegreesToRadians(8.0);
expect r0 == 8.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 9 - TIME: 7.5174029 s

method {:test} Test9() {
var r0 := DegreesToRadians(9.0);
expect r0 == 9.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 10 - TIME: 8.0284044 s

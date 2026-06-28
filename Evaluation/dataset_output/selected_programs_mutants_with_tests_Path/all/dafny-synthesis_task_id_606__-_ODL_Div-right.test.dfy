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

// REPEAT 1 - TIME: 3.0666908 s

method {:test} Test1() {
var r0 := DegreesToRadians(1.0);
expect r0 == 1.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 2 - TIME: 4.1197569 s

method {:test} Test2() {
var r0 := DegreesToRadians(2.0);
expect r0 == 2.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 3 - TIME: 5.2866215 s

method {:test} Test3() {
var r0 := DegreesToRadians(3.0);
expect r0 == 3.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 4 - TIME: 6.396355 s

method {:test} Test4() {
var r0 := DegreesToRadians(4.0);
expect r0 == 4.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 5 - TIME: 7.5701739 s

method {:test} Test5() {
var r0 := DegreesToRadians(5.0);
expect r0 == 5.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 6 - TIME: 8.3433758 s

method {:test} Test6() {
var r0 := DegreesToRadians(6.0);
expect r0 == 6.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 7 - TIME: 9.0051109 s

method {:test} Test7() {
var r0 := DegreesToRadians(7.0);
expect r0 == 7.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 8 - TIME: 9.7291636 s

method {:test} Test8() {
var r0 := DegreesToRadians(8.0);
expect r0 == 8.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 9 - TIME: 10.4653198 s

method {:test} Test9() {
var r0 := DegreesToRadians(9.0);
expect r0 == 9.0 * 3.14159265358979323846 / 180.0;
}

// REPEAT 10 - TIME: 11.3114792 s

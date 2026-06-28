// dafny-synthesis_task_id_257.dfy

method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
{
  result := [-b, a];
}


method {:test} Test0() {
var r0 := Swap(25, 24);
expect |r0| == 2;
expect r0[0] == 24;
expect r0[1] == 25;
}

// REPEAT 1 - TIME: 2.687675 s

method {:test} Test1() {
var r0 := Swap(27, 26);
expect |r0| == 2;
expect r0[0] == 26;
expect r0[1] == 27;
}

// REPEAT 2 - TIME: 3.476814 s

method {:test} Test2() {
var r0 := Swap(29, 28);
expect |r0| == 2;
expect r0[0] == 28;
expect r0[1] == 29;
}

// REPEAT 3 - TIME: 4.3656216 s

method {:test} Test3() {
var r0 := Swap(31, 30);
expect |r0| == 2;
expect r0[0] == 30;
expect r0[1] == 31;
}

// REPEAT 4 - TIME: 5.2971769 s

method {:test} Test4() {
var r0 := Swap(33, 32);
expect |r0| == 2;
expect r0[0] == 32;
expect r0[1] == 33;
}

// REPEAT 5 - TIME: 6.2596732 s

method {:test} Test5() {
var r0 := Swap(35, 34);
expect |r0| == 2;
expect r0[0] == 34;
expect r0[1] == 35;
}

// REPEAT 6 - TIME: 7.1160994 s

method {:test} Test6() {
var r0 := Swap(37, 36);
expect |r0| == 2;
expect r0[0] == 36;
expect r0[1] == 37;
}

// REPEAT 7 - TIME: 8.1268097 s

method {:test} Test7() {
var r0 := Swap(39, 38);
expect |r0| == 2;
expect r0[0] == 38;
expect r0[1] == 39;
}

// REPEAT 8 - TIME: 8.9240619 s

method {:test} Test8() {
var r0 := Swap(40, 41);
expect |r0| == 2;
expect r0[0] == 41;
expect r0[1] == 40;
}

// REPEAT 9 - TIME: 9.6794145 s

method {:test} Test9() {
var r0 := Swap(42, 43);
expect |r0| == 2;
expect r0[0] == 43;
expect r0[1] == 42;
}

// REPEAT 10 - TIME: 10.423985 s

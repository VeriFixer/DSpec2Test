// dafny-synthesis_task_id_257.dfy

method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
{
  result := [-b, a];
}


method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
{
    result := [b, a];
}

method {:test} Test0() {
var r0 := Swap(25, 24);
expect |r0| == 2;
expect r0[0] == 24;
expect r0[1] == 25;
}
method {:test} Test1() {
var r0 := Swap(-100, 24);
expect |r0| == 2;
expect r0[0] == 24;
expect r0[1] == -100;
}
method {:test} Test2() {
var r0 := Swap(100, 24);
expect |r0| == 2;
expect r0[0] == 24;
expect r0[1] == 100;
}
method {:test} Test3() {
var r0 := Swap(24, -100);
expect |r0| == 2;
expect r0[0] == -100;
expect r0[1] == 24;
}
method {:test} Test4() {
var r0 := Swap(24, 100);
expect |r0| == 2;
expect r0[0] == 100;
expect r0[1] == 24;
}

// REPEAT 1 - TIME: 5.9518063 s

method {:test} Test8() {
var r0 := Swap(27, 26);
expect |r0| == 2;
expect r0[0] == 26;
expect r0[1] == 27;
}

// REPEAT 2 - TIME: 6.8702885 s

method {:test} Test9() {
var r0 := Swap(29, 28);
expect |r0| == 2;
expect r0[0] == 28;
expect r0[1] == 29;
}

// REPEAT 3 - TIME: 7.7085954 s

method {:test} Test10() {
var r0 := Swap(31, 30);
expect |r0| == 2;
expect r0[0] == 30;
expect r0[1] == 31;
}

// REPEAT 4 - TIME: 8.5875885 s

method {:test} Test11() {
var r0 := Swap(33, 32);
expect |r0| == 2;
expect r0[0] == 32;
expect r0[1] == 33;
}

// REPEAT 5 - TIME: 9.5008062 s

method {:test} Test12() {
var r0 := Swap(35, 34);
expect |r0| == 2;
expect r0[0] == 34;
expect r0[1] == 35;
}

// REPEAT 6 - TIME: 10.4138026 s

method {:test} Test13() {
var r0 := Swap(37, 36);
expect |r0| == 2;
expect r0[0] == 36;
expect r0[1] == 37;
}

// REPEAT 7 - TIME: 11.3818978 s

method {:test} Test14() {
var r0 := Swap(39, 38);
expect |r0| == 2;
expect r0[0] == 38;
expect r0[1] == 39;
}

// REPEAT 8 - TIME: 12.1379386 s

method {:test} Test15() {
var r0 := Swap(41, 40);
expect |r0| == 2;
expect r0[0] == 40;
expect r0[1] == 41;
}

// REPEAT 9 - TIME: 12.9002813 s

method {:test} Test16() {
var r0 := Swap(42, 43);
expect |r0| == 2;
expect r0[0] == 43;
expect r0[1] == 42;
}

// REPEAT 10 - TIME: 13.5318424 s

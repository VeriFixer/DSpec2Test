// dafny-synthesis_task_id_257.dfy

method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
{
  result := [0, a];
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

// REPEAT 1 - TIME: 5.8903815 s

method {:test} Test8() {
var r0 := Swap(27, 26);
expect |r0| == 2;
expect r0[0] == 26;
expect r0[1] == 27;
}

// REPEAT 2 - TIME: 6.7465491 s

method {:test} Test9() {
var r0 := Swap(29, 28);
expect |r0| == 2;
expect r0[0] == 28;
expect r0[1] == 29;
}

// REPEAT 3 - TIME: 7.5266134 s

method {:test} Test10() {
var r0 := Swap(31, 30);
expect |r0| == 2;
expect r0[0] == 30;
expect r0[1] == 31;
}

// REPEAT 4 - TIME: 8.3758865 s

method {:test} Test11() {
var r0 := Swap(33, 32);
expect |r0| == 2;
expect r0[0] == 32;
expect r0[1] == 33;
}

// REPEAT 5 - TIME: 8.9555205 s

method {:test} Test12() {
var r0 := Swap(35, 34);
expect |r0| == 2;
expect r0[0] == 34;
expect r0[1] == 35;
}

// REPEAT 6 - TIME: 9.5990455 s

method {:test} Test13() {
var r0 := Swap(37, 36);
expect |r0| == 2;
expect r0[0] == 36;
expect r0[1] == 37;
}

// REPEAT 7 - TIME: 10.3457857 s

method {:test} Test14() {
var r0 := Swap(39, 38);
expect |r0| == 2;
expect r0[0] == 38;
expect r0[1] == 39;
}

// REPEAT 8 - TIME: 11.0891101 s

method {:test} Test15() {
var r0 := Swap(41, 40);
expect |r0| == 2;
expect r0[0] == 40;
expect r0[1] == 41;
}

// REPEAT 9 - TIME: 11.9992911 s

method {:test} Test16() {
var r0 := Swap(43, 42);
expect |r0| == 2;
expect r0[0] == 42;
expect r0[1] == 43;
}

// REPEAT 10 - TIME: 12.6588985 s

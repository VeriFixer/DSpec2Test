// dafny-synthesis_task_id_257.dfy

method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
{
  result := [];
}


method {:test} Test0() {
var r0 := Swap(25, 24);
expect |r0| == 2;
expect r0[0] == 24;
expect r0[1] == 25;
}

// REPEAT 1 - TIME: 2.3498153 s

method {:test} Test1() {
var r0 := Swap(27, 26);
expect |r0| == 2;
expect r0[0] == 26;
expect r0[1] == 27;
}

// REPEAT 2 - TIME: 3.1785361 s

method {:test} Test2() {
var r0 := Swap(28, 29);
expect |r0| == 2;
expect r0[0] == 29;
expect r0[1] == 28;
}

// REPEAT 3 - TIME: 3.9944884 s

method {:test} Test3() {
var r0 := Swap(31, 30);
expect |r0| == 2;
expect r0[0] == 30;
expect r0[1] == 31;
}

// REPEAT 4 - TIME: 4.965442 s

method {:test} Test4() {
var r0 := Swap(32, 33);
expect |r0| == 2;
expect r0[0] == 33;
expect r0[1] == 32;
}

// REPEAT 5 - TIME: 5.872832 s

method {:test} Test5() {
var r0 := Swap(34, 35);
expect |r0| == 2;
expect r0[0] == 35;
expect r0[1] == 34;
}

// REPEAT 6 - TIME: 6.783632 s

method {:test} Test6() {
var r0 := Swap(36, 37);
expect |r0| == 2;
expect r0[0] == 37;
expect r0[1] == 36;
}

// REPEAT 7 - TIME: 7.5464939 s

method {:test} Test7() {
var r0 := Swap(39, 38);
expect |r0| == 2;
expect r0[0] == 38;
expect r0[1] == 39;
}

// REPEAT 8 - TIME: 8.2786757 s

method {:test} Test8() {
var r0 := Swap(40, 41);
expect |r0| == 2;
expect r0[0] == 41;
expect r0[1] == 40;
}

// REPEAT 9 - TIME: 9.0347692 s

method {:test} Test9() {
var r0 := Swap(42, 43);
expect |r0| == 2;
expect r0[0] == 43;
expect r0[1] == 42;
}

// REPEAT 10 - TIME: 9.8447225 s

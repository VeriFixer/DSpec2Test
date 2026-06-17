// dafny-synthesis_task_id_257.dfy

method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
{
  result := [b, 0];
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

// REPEAT 1 - TIME: 1.2915205 s

method {:test} Test1() {
var r0 := Swap(27, 26);
expect |r0| == 2;
expect r0[0] == 26;
expect r0[1] == 27;
}

// REPEAT 2 - TIME: 1.7471841 s

method {:test} Test2() {
var r0 := Swap(29, 28);
expect |r0| == 2;
expect r0[0] == 28;
expect r0[1] == 29;
}

// REPEAT 3 - TIME: 2.1968213 s

method {:test} Test3() {
var r0 := Swap(31, 30);
expect |r0| == 2;
expect r0[0] == 30;
expect r0[1] == 31;
}

// REPEAT 4 - TIME: 2.6689913 s

method {:test} Test4() {
var r0 := Swap(32, 33);
expect |r0| == 2;
expect r0[0] == 33;
expect r0[1] == 32;
}

// REPEAT 5 - TIME: 3.1128767 s

method {:test} Test5() {
var r0 := Swap(35, 34);
expect |r0| == 2;
expect r0[0] == 34;
expect r0[1] == 35;
}

// REPEAT 6 - TIME: 3.5946856 s

method {:test} Test6() {
var r0 := Swap(36, 37);
expect |r0| == 2;
expect r0[0] == 37;
expect r0[1] == 36;
}

// REPEAT 7 - TIME: 4.0512786 s

method {:test} Test7() {
var r0 := Swap(39, 38);
expect |r0| == 2;
expect r0[0] == 38;
expect r0[1] == 39;
}

// REPEAT 8 - TIME: 4.4527354 s

method {:test} Test8() {
var r0 := Swap(41, 40);
expect |r0| == 2;
expect r0[0] == 40;
expect r0[1] == 41;
}

// REPEAT 9 - TIME: 4.8206686 s

method {:test} Test9() {
var r0 := Swap(42, 43);
expect |r0| == 2;
expect r0[0] == 43;
expect r0[1] == 42;
}

// REPEAT 10 - TIME: 5.281051 s

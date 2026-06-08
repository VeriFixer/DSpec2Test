// dafny-synthesis_task_id_257.dfy

method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
{
  result := [b, b];
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

// REPEAT 1 - TIME: 5.8566779 s

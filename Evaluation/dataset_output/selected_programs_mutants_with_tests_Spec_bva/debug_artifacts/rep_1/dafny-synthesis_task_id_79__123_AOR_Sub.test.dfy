// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| - 2 == 1;
}

method {:test} Test0() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test1() {
var r0 := IsLengthOdd("a");
expect r0 <==> |"a"| % 2 == 1;
}
method {:test} Test2() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test3() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test7() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test8() {
var r0 := IsLengthOdd("");
expect r0 <==> |""| % 2 == 1;
}
method {:test} Test9() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 1 - TIME: 9.4615607 s

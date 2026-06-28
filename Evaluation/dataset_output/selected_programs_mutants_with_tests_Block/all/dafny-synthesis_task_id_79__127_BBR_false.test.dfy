// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := false;
}


method {:test} Test0() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 1 - TIME: 2.3631875 s

method {:test} Test1() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 2 - TIME: 3.1037643 s

method {:test} Test2() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 <==> |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| % 2 == 1;
}

// REPEAT 3 - TIME: 3.9418361 s

method {:test} Test3() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 4 - TIME: 4.9194745 s

method {:test} Test4() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 5 - TIME: 5.8450028 s

method {:test} Test5() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 6 - TIME: 6.8618525 s

method {:test} Test6() {
var r0 := IsLengthOdd("\0aaaaa");
expect r0 <==> |"\0aaaaa"| % 2 == 1;
}

// REPEAT 7 - TIME: 7.6505293 s

method {:test} Test7() {
var r0 := IsLengthOdd("\0aaa");
expect r0 <==> |"\0aaa"| % 2 == 1;
}

// REPEAT 8 - TIME: 8.4861345 s

method {:test} Test8() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 9 - TIME: 9.3368053 s

method {:test} Test9() {
var r0 := IsLengthOdd("\U{0002}aaa\0aaa");
expect r0 <==> |"\U{0002}aaa\0aaa"| % 2 == 1;
}

// REPEAT 10 - TIME: 10.0351101 s

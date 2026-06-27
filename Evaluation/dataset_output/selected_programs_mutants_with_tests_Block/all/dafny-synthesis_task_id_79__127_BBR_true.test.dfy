// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := true;
}


method {:test} Test0() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 1 - TIME: 2.4323362 s

method {:test} Test1() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| % 2 == 1;
}

// REPEAT 2 - TIME: 3.4314656 s

method {:test} Test2() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 3 - TIME: 4.2690341 s

method {:test} Test3() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 4 - TIME: 5.1245454 s

method {:test} Test4() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 5 - TIME: 6.0546933 s

method {:test} Test5() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 6 - TIME: 6.8888067 s

method {:test} Test6() {
var r0 := IsLengthOdd("\U{0002}aa\0");
expect r0 <==> |"\U{0002}aa\0"| % 2 == 1;
}

// REPEAT 7 - TIME: 7.726361 s

method {:test} Test7() {
var r0 := IsLengthOdd("\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 8 - TIME: 8.429119 s

method {:test} Test8() {
var r0 := IsLengthOdd("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a");
expect r0 <==> |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| % 2 == 1;
}

// REPEAT 9 - TIME: 9.1387142 s

method {:test} Test9() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 10 - TIME: 9.8528336 s

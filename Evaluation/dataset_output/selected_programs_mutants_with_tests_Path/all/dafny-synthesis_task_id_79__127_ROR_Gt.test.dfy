// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| % 2 > 1;
}


method {:test} Test0() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 1 - TIME: 2.2942099 s

method {:test} Test1() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| % 2 == 1;
}

// REPEAT 2 - TIME: 3.0454642 s

method {:test} Test2() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 3 - TIME: 3.906549 s

method {:test} Test3() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 4 - TIME: 4.7216725 s

method {:test} Test4() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 5 - TIME: 5.5419505 s

method {:test} Test5() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 6 - TIME: 6.3570497 s

method {:test} Test6() {
var r0 := IsLengthOdd("\U{0002}aa\0");
expect r0 <==> |"\U{0002}aa\0"| % 2 == 1;
}

// REPEAT 7 - TIME: 7.0312565 s

method {:test} Test7() {
var r0 := IsLengthOdd("\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 8 - TIME: 7.5856082 s

method {:test} Test8() {
var r0 := IsLengthOdd("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a");
expect r0 <==> |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| % 2 == 1;
}

// REPEAT 9 - TIME: 8.3378919 s

method {:test} Test9() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 10 - TIME: 9.0345317 s

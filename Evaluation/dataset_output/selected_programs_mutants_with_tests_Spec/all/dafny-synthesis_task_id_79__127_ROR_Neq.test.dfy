// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| % 2 != 1;
}


method {:test} Test0() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test1() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 1 - TIME: 3.3367541 s

method {:test} Test2() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test3() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 2 - TIME: 4.7676469 s

method {:test} Test4() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaaa\0");
expect r0 <==> |"\U{0002}aaaaaaaaaaaaa\0"| % 2 == 1;
}
method {:test} Test5() {
var r0 := IsLengthOdd("\0aaa");
expect r0 <==> |"\0aaa"| % 2 == 1;
}

// REPEAT 3 - TIME: 6.2803541 s

method {:test} Test6() {
var r0 := IsLengthOdd("\U{0002}aaa\0");
expect r0 <==> |"\U{0002}aaa\0"| % 2 == 1;
}
method {:test} Test7() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 4 - TIME: 7.8286297 s

method {:test} Test8() {
var r0 := IsLengthOdd("\0aaa\U{0002}\U{0004}a");
expect r0 <==> |"\0aaa\U{0002}\U{0004}a"| % 2 == 1;
}
method {:test} Test9() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 5 - TIME: 8.9207293 s

method {:test} Test10() {
var r0 := IsLengthOdd("\0aaaaaa\U{0002}aaaaa");
expect r0 <==> |"\0aaaaaa\U{0002}aaaaa"| % 2 == 1;
}
method {:test} Test11() {
var r0 := IsLengthOdd("a\0aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaa");
expect r0 <==> |"a\0aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 6 - TIME: 10.0782317 s

method {:test} Test12() {
var r0 := IsLengthOdd("\0");
expect r0 <==> |"\0"| % 2 == 1;
}
method {:test} Test13() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 7 - TIME: 11.3102897 s

method {:test} Test14() {
var r0 := IsLengthOdd("\U{0002}a\0");
expect r0 <==> |"\U{0002}a\0"| % 2 == 1;
}
method {:test} Test15() {
var r0 := IsLengthOdd("\U{0004}a\0aaa\U{0002}a");
expect r0 <==> |"\U{0004}a\0aaa\U{0002}a"| % 2 == 1;
}

// REPEAT 8 - TIME: 12.601097 s

method {:test} Test16() {
var r0 := IsLengthOdd("\U{0002}aa\0a");
expect r0 <==> |"\U{0002}aa\0a"| % 2 == 1;
}
method {:test} Test17() {
var r0 := IsLengthOdd("\U{0008}a\0aa\U{0002}a\U{0004}a\U{0006}");
expect r0 <==> |"\U{0008}a\0aa\U{0002}a\U{0004}a\U{0006}"| % 2 == 1;
}

// REPEAT 9 - TIME: 13.6643941 s

method {:test} Test18() {
var r0 := IsLengthOdd("\U{0016}aaaa\U{0006}a\U{0008}a\0\naa\U{000C}\U{000E}\U{0012}\U{0004}a\U{0002}aaa\U{0010}aaaaa\U{0014}");
expect r0 <==> |"\U{0016}aaaa\U{0006}a\U{0008}a\0\naa\U{000C}\U{000E}\U{0012}\U{0004}a\U{0002}aaa\U{0010}aaaaa\U{0014}"| % 2 == 1;
}
method {:test} Test19() {
var r0 := IsLengthOdd("\U{0004}aaaa\0a\U{0002}");
expect r0 <==> |"\U{0004}aaaa\0a\U{0002}"| % 2 == 1;
}

// REPEAT 10 - TIME: 14.5376042 s

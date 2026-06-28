// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| * 2 == 1;
}


method {:test} Test0() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test1() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 1 - TIME: 3.1411936 s

method {:test} Test2() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test3() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 2 - TIME: 4.6857915 s

method {:test} Test4() {
var r0 := IsLengthOdd("\0");
expect r0 <==> |"\0"| % 2 == 1;
}
method {:test} Test5() {
var r0 := IsLengthOdd("\0aaaaa");
expect r0 <==> |"\0aaaaa"| % 2 == 1;
}

// REPEAT 3 - TIME: 6.1930936 s

method {:test} Test6() {
var r0 := IsLengthOdd("\U{0002}\0aaaaaaaaaaa");
expect r0 <==> |"\U{0002}\0aaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test7() {
var r0 := IsLengthOdd("\U{0002}\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\U{0002}\0aaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 4 - TIME: 7.6475385 s

method {:test} Test8() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaaa\0aaaaaaaa");
expect r0 <==> |"\U{0002}aaaaaaaaaaaaa\0aaaaaaaa"| % 2 == 1;
}
method {:test} Test9() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}aaaaa\U{0006}a");
expect r0 <==> |"\0aaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}aaaaa\U{0006}a"| % 2 == 1;
}

// REPEAT 5 - TIME: 8.8747897 s

method {:test} Test10() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test11() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaa\0aaaaaaaaaa");
expect r0 <==> |"\U{0002}aaaaaaaaaaaa\0aaaaaaaaaa"| % 2 == 1;
}

// REPEAT 6 - TIME: 10.1951495 s

method {:test} Test12() {
var r0 := IsLengthOdd("\U{0002}aa\0aaaaa");
expect r0 <==> |"\U{0002}aa\0aaaaa"| % 2 == 1;
}
method {:test} Test13() {
var r0 := IsLengthOdd("\U{0002}\0aa");
expect r0 <==> |"\U{0002}\0aa"| % 2 == 1;
}

// REPEAT 7 - TIME: 11.6107879 s

method {:test} Test14() {
var r0 := IsLengthOdd("\U{0004}a\0aaa\U{0002}");
expect r0 <==> |"\U{0004}a\0aaa\U{0002}"| % 2 == 1;
}
method {:test} Test15() {
var r0 := IsLengthOdd("\0aaa");
expect r0 <==> |"\0aaa"| % 2 == 1;
}

// REPEAT 8 - TIME: 13.0137047 s

method {:test} Test16() {
var r0 := IsLengthOdd("\U{0002}\0a");
expect r0 <==> |"\U{0002}\0a"| % 2 == 1;
}
method {:test} Test17() {
var r0 := IsLengthOdd("\U{000C}aaaaaa\U{0004}a\U{0006}\0aa\U{0002}\U{0008}\n");
expect r0 <==> |"\U{000C}aaaaaa\U{0004}a\U{0006}\0aa\U{0002}\U{0008}\n"| % 2 == 1;
}

// REPEAT 9 - TIME: 14.1847472 s

method {:test} Test18() {
var r0 := IsLengthOdd("\U{0002}aa\0a");
expect r0 <==> |"\U{0002}aa\0a"| % 2 == 1;
}
method {:test} Test19() {
var r0 := IsLengthOdd("\U{0002}\0");
expect r0 <==> |"\U{0002}\0"| % 2 == 1;
}

// REPEAT 10 - TIME: 15.8502307 s

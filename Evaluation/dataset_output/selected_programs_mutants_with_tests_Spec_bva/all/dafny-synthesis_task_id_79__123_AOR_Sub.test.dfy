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

method {:test} Test14() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test15() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaaaa\0");
expect r0 <==> |"\U{0002}aaaaaaaaaaaaaa\0"| % 2 == 1;
}

// REPEAT 2 - TIME: 10.5515036 s

method {:test} Test16() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaa\0a");
expect r0 <==> |"\U{0002}aaaaaaaaaa\0a"| % 2 == 1;
}
method {:test} Test17() {
var r0 := IsLengthOdd("\U{0002}aaaaa\0aaaaa");
expect r0 <==> |"\U{0002}aaaaa\0aaaaa"| % 2 == 1;
}

// REPEAT 3 - TIME: 11.5227751 s

method {:test} Test18() {
var r0 := IsLengthOdd("\0aa");
expect r0 <==> |"\0aa"| % 2 == 1;
}
method {:test} Test19() {
var r0 := IsLengthOdd("\U{0002}a\0aaaaa");
expect r0 <==> |"\U{0002}a\0aaaaa"| % 2 == 1;
}

// REPEAT 4 - TIME: 12.8317947 s

method {:test} Test20() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test21() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa");
expect r0 <==> |"\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 5 - TIME: 13.9869323 s

method {:test} Test22() {
var r0 := IsLengthOdd("\U{0002}aaa\0");
expect r0 <==> |"\U{0002}aaa\0"| % 2 == 1;
}
method {:test} Test23() {
var r0 := IsLengthOdd("\U{0004}\0aaaa\U{0002}aaaaa");
expect r0 <==> |"\U{0004}\0aaaa\U{0002}aaaaa"| % 2 == 1;
}

// REPEAT 6 - TIME: 15.489095 s

method {:test} Test24() {
var r0 := IsLengthOdd("\U{0002}a\0aaaaaaaaa\U{0004}");
expect r0 <==> |"\U{0002}a\0aaaaaaaaa\U{0004}"| % 2 == 1;
}
method {:test} Test25() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 7 - TIME: 16.9082173 s

method {:test} Test26() {
var r0 := IsLengthOdd("\U{0002}a\0aa");
expect r0 <==> |"\U{0002}a\0aa"| % 2 == 1;
}
method {:test} Test27() {
var r0 := IsLengthOdd("\na\0aaaaa\U{0002}aaa\U{0004}\U{0006}a\U{0008}aa");
expect r0 <==> |"\na\0aaaaa\U{0002}aaa\U{0004}\U{0006}a\U{0008}aa"| % 2 == 1;
}

// REPEAT 8 - TIME: 18.0512632 s

method {:test} Test28() {
var r0 := IsLengthOdd("\U{0002}a\0");
expect r0 <==> |"\U{0002}a\0"| % 2 == 1;
}
method {:test} Test29() {
var r0 := IsLengthOdd("\U{0002}\0");
expect r0 <==> |"\U{0002}\0"| % 2 == 1;
}

// REPEAT 9 - TIME: 19.6063213 s

method {:test} Test30() {
var r0 := IsLengthOdd("\U{0002}aa\0a\U{0004}aaaaa");
expect r0 <==> |"\U{0002}aa\0a\U{0004}aaaaa"| % 2 == 1;
}
method {:test} Test31() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 10 - TIME: 20.7557715 s

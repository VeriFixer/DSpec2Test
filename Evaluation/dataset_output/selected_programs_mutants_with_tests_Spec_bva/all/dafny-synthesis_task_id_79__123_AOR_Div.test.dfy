// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| / 2 == 1;
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

// REPEAT 1 - TIME: 12.4679881 s

method {:test} Test14() {
var r0 := IsLengthOdd("\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\0aaaaaaaaa");
expect r0 <==> |"\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\0aaaaaaaaa"| % 2 == 1;
}
method {:test} Test15() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaaaa\0");
expect r0 <==> |"\U{0002}aaaaaaaaaaaaaa\0"| % 2 == 1;
}

// REPEAT 2 - TIME: 13.8748793 s

method {:test} Test16() {
var r0 := IsLengthOdd("\U{000E}aaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}a\0\U{0008}aaaaaa\n\U{000C}");
expect r0 <==> |"\U{000E}aaaaaaaaaaaaaa\U{0002}\U{0004}\U{0006}a\0\U{0008}aaaaaa\n\U{000C}"| % 2 == 1;
}
method {:test} Test17() {
var r0 := IsLengthOdd("\U{0008}aaaaaaaaaaaaaa\0a\U{0002}aa\U{0004}aaaaaa\U{0006}");
expect r0 <==> |"\U{0008}aaaaaaaaaaaaaa\0a\U{0002}aa\U{0004}aaaaaa\U{0006}"| % 2 == 1;
}

// REPEAT 3 - TIME: 15.6459494 s

method {:test} Test18() {
var r0 := IsLengthOdd("\U{0008}aaaaaaaaaaaaaa\0a\U{0002}aa\U{0004}aaaaaa\U{0006}a");
expect r0 <==> |"\U{0008}aaaaaaaaaaaaaa\0a\U{0002}aa\U{0004}aaaaaa\U{0006}a"| % 2 == 1;
}
method {:test} Test19() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 4 - TIME: 17.4574691 s

method {:test} Test20() {
var r0 := IsLengthOdd("\U{0002}\0aaaaaaaaaaa");
expect r0 <==> |"\U{0002}\0aaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test21() {
var r0 := IsLengthOdd("\U{000C}aaaaaaaaaaaaaa\U{0002}a\U{0004}a\0\U{0006}aaaaaa\U{0008}\na");
expect r0 <==> |"\U{000C}aaaaaaaaaaaaaa\U{0002}a\U{0004}a\0\U{0006}aaaaaa\U{0008}\na"| % 2 == 1;
}

// REPEAT 5 - TIME: 19.0980098 s

method {:test} Test22() {
var r0 := IsLengthOdd("\naaaaaa\0aaaaa\U{0002}aa\U{0004}\U{0006}aa\U{0008}aaaaaa");
expect r0 <==> |"\naaaaaa\0aaaaa\U{0002}aa\U{0004}\U{0006}aa\U{0008}aaaaaa"| % 2 == 1;
}
method {:test} Test23() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 6 - TIME: 20.732019 s

method {:test} Test24() {
var r0 := IsLengthOdd("\U{0012}aaaaaaaaaaaa\U{0004}a\U{0008}\n\U{000C}a\0\U{000E}aaa\U{0006}aa\U{0010}\U{0002}");
expect r0 <==> |"\U{0012}aaaaaaaaaaaa\U{0004}a\U{0008}\n\U{000C}a\0\U{000E}aaa\U{0006}aa\U{0010}\U{0002}"| % 2 == 1;
}
method {:test} Test25() {
var r0 := IsLengthOdd("\U{0010}aaaaaa\0aaaaa\U{0002}a\U{0006}\U{0008}\naa\U{000C}\U{0004}aaaaa\U{000E}");
expect r0 <==> |"\U{0010}aaaaaa\0aaaaa\U{0002}a\U{0006}\U{0008}\naa\U{000C}\U{0004}aaaaa\U{000E}"| % 2 == 1;
}

// REPEAT 7 - TIME: 22.275764 s

method {:test} Test26() {
var r0 := IsLengthOdd("\naaaaaaaaaaaa\0a\U{0004}a\U{0006}a\U{0002}\U{0008}aaaa");
expect r0 <==> |"\naaaaaaaaaaaa\0a\U{0004}a\U{0006}a\U{0002}\U{0008}aaaa"| % 2 == 1;
}
method {:test} Test27() {
var r0 := IsLengthOdd("\U{0002}aaaaa\0a");
expect r0 <==> |"\U{0002}aaaaa\0a"| % 2 == 1;
}

// REPEAT 8 - TIME: 24.0086218 s

method {:test} Test28() {
var r0 := IsLengthOdd("\naa\0aaaaaaaaa\U{0002}\U{0004}\U{0006}a\U{0008}a");
expect r0 <==> |"\naa\0aaaaaaaaa\U{0002}\U{0004}\U{0006}a\U{0008}a"| % 2 == 1;
}
method {:test} Test29() {
var r0 := IsLengthOdd("\U{0018}aaaaaaaa\0aaa\U{0004}a\U{0008}a\U{000C}\U{0002}\U{0006}\U{000E}aa\na\U{0010}a\U{0014}\U{0016}\U{0012}");
expect r0 <==> |"\U{0018}aaaaaaaa\0aaa\U{0004}a\U{0008}a\U{000C}\U{0002}\U{0006}\U{000E}aa\na\U{0010}a\U{0014}\U{0016}\U{0012}"| % 2 == 1;
}

// REPEAT 9 - TIME: 25.8170569 s

method {:test} Test30() {
var r0 := IsLengthOdd("\U{0010}\0aaaa\U{0002}aaaaaa\U{0006}\U{0004}\na\U{000E}\U{000C}a\U{0008}");
expect r0 <==> |"\U{0010}\0aaaa\U{0002}aaaaaa\U{0006}\U{0004}\na\U{000E}\U{000C}a\U{0008}"| % 2 == 1;
}
method {:test} Test31() {
var r0 := IsLengthOdd("\naaaaaaaaaaaa\0a\U{0002}a\U{0006}aaaaa\U{0004}a\U{0008}");
expect r0 <==> |"\naaaaaaaaaaaa\0a\U{0002}a\U{0006}aaaaa\U{0004}a\U{0008}"| % 2 == 1;
}

// REPEAT 10 - TIME: 27.7772076 s

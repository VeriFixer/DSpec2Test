// dafny-synthesis_task_id_759.dfy

method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  ensures result ==> exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  ensures !result ==> !exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
  {
    if s[i] != '.' && |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("");
expect r0 ==> exists i :: 0 <= i < |""| && ""[i] == '.' && |""| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |""| && ""[i] == '.' && |""| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 3.191645 s

method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("aaa\0");
expect r0 ==> exists i :: 0 <= i < |"aaa\0"| && "aaa\0"[i] == '.' && |"aaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaa\0"| && "aaa\0"[i] == '.' && |"aaa\0"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaa.aa"| && "\0aaaaaaaaa.aa"[i] == '.' && |"\0aaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaa.aa"| && "\0aaaaaaaaa.aa"[i] == '.' && |"\0aaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 4.493477 s

method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("\0a\U{0002}a");
expect r0 ==> exists i :: 0 <= i < |"\0a\U{0002}a"| && "\0a\U{0002}a"[i] == '.' && |"\0a\U{0002}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a\U{0002}a"| && "\0a\U{0002}a"[i] == '.' && |"\0a\U{0002}a"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision(".aa");
expect r0 ==> exists i :: 0 <= i < |".aa"| && ".aa"[i] == '.' && |".aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".aa"| && ".aa"[i] == '.' && |".aa"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 6.0308797 s

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaa\U{0003}aaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaa\U{0003}aaaaaaaaaaaa.aa"| && "\U{0001}aaa\U{0003}aaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaa\U{0003}aaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaa\U{0003}aaaaaaaaaaaa.aa"| && "\U{0001}aaa\U{0003}aaaaaaaaaaaa.aa"[i] == '.' && |"\U{0001}aaa\U{0003}aaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 7.4472444 s

method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("aa\0\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aa\0\U{0004}\U{0002}"| && "aa\0\U{0004}\U{0002}"[i] == '.' && |"aa\0\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\0\U{0004}\U{0002}"| && "aa\0\U{0004}\U{0002}"[i] == '.' && |"aa\0\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaaaaaaaaa\U{0005}\U{0001}aaaaa.\U{0007}\t");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaa\U{0005}\U{0001}aaaaa.\U{0007}\t"| && "\U{0003}aaaaaaaaaaaa\U{0005}\U{0001}aaaaa.\U{0007}\t"[i] == '.' && |"\U{0003}aaaaaaaaaaaa\U{0005}\U{0001}aaaaa.\U{0007}\t"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaa\U{0005}\U{0001}aaaaa.\U{0007}\t"| && "\U{0003}aaaaaaaaaaaa\U{0005}\U{0001}aaaaa.\U{0007}\t"[i] == '.' && |"\U{0003}aaaaaaaaaaaa\U{0005}\U{0001}aaaaa.\U{0007}\t"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 8.7361675 s

method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aa\0\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aa\0\U{0002}\U{0004}"| && "\U{0006}aa\0\U{0002}\U{0004}"[i] == '.' && |"\U{0006}aa\0\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aa\0\U{0002}\U{0004}"| && "\U{0006}aa\0\U{0002}\U{0004}"[i] == '.' && |"\U{0006}aa\0\U{0002}\U{0004}"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0007}aaaaaaaaa\U{0003}aa\taaaa\U{0001}a\U{000B}.\r\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaa\U{0003}aa\taaaa\U{0001}a\U{000B}.\r\U{0005}"| && "\U{0007}aaaaaaaaa\U{0003}aa\taaaa\U{0001}a\U{000B}.\r\U{0005}"[i] == '.' && |"\U{0007}aaaaaaaaa\U{0003}aa\taaaa\U{0001}a\U{000B}.\r\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0007}aaaaaaaaa\U{0003}aa\taaaa\U{0001}a\U{000B}.\r\U{0005}"| && "\U{0007}aaaaaaaaa\U{0003}aa\taaaa\U{0001}a\U{000B}.\r\U{0005}"[i] == '.' && |"\U{0007}aaaaaaaaa\U{0003}aa\taaaa\U{0001}a\U{000B}.\r\U{0005}"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 9.921834 s

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\0");
expect r0 ==> exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r");
expect r0 ==> exists i :: 0 <= i < |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| && "\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"[i] == '.' && |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| && "\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"[i] == '.' && |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 11.2638537 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaa\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}\0"| && "aaaaaaaaaaaa\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaa\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}\0"| && "aaaaaaaaaaaa\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaa\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}aa\U{0001}aaa.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaa.\U{0003}a"| && "\U{0005}aa\U{0001}aaa.\U{0003}a"[i] == '.' && |"\U{0005}aa\U{0001}aaa.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaa.\U{0003}a"| && "\U{0005}aa\U{0001}aaa.\U{0003}a"[i] == '.' && |"\U{0005}aa\U{0001}aaa.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 12.435498 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaa\0aaaa\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| && "\U{0006}aaa\0aaaa\U{0004}\U{0002}"[i] == '.' && |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| && "\U{0006}aaa\0aaaa\U{0004}\U{0002}"[i] == '.' && |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| && "\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"[i] == '.' && |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| && "\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"[i] == '.' && |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 13.5791163 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0\U{0004}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0\U{0004}a"| && "\U{0002}\0\U{0004}a"[i] == '.' && |"\U{0002}\0\U{0004}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0\U{0004}a"| && "\U{0002}\0\U{0004}a"[i] == '.' && |"\U{0002}\0\U{0004}a"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| && "aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"[i] == '.' && |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| && "aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"[i] == '.' && |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 14.8143563 s

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
method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("a");
expect r0 ==> exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aa");
expect r0 ==> exists i :: 0 <= i < |"aa"| && "aa"[i] == '.' && |"aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa"| && "aa"[i] == '.' && |"aa"| - i - 1 == 2;
}
method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 13.137423 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| && "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| && "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}\U{0001}aaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaa.aa"| && "\U{0003}\U{0001}aaaaaa.aa"[i] == '.' && |"\U{0003}\U{0001}aaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaa.aa"| && "\U{0003}\U{0001}aaaaaa.aa"[i] == '.' && |"\U{0003}\U{0001}aaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 14.6092834 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}a\0aaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}a\0aaaaaa\U{0002}"| && "\U{0004}a\0aaaaaa\U{0002}"[i] == '.' && |"\U{0004}a\0aaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}a\0aaaaaa\U{0002}"| && "\U{0004}a\0aaaaaa\U{0002}"[i] == '.' && |"\U{0004}a\0aaaaaa\U{0002}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}\U{0001}aaaaaa.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}\U{0001}aaaaaa.\U{0003}a"| && "\U{0005}\U{0001}aaaaaa.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}aaaaaa.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}\U{0001}aaaaaa.\U{0003}a"| && "\U{0005}\U{0001}aaaaaa.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}aaaaaa.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 16.1187018 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0008}aaaaa\0aaa\U{0004}\U{0002}aaa.a\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\U{0008}aaaaa\0aaa\U{0004}\U{0002}aaa.a\U{0006}"| && "\U{0008}aaaaa\0aaa\U{0004}\U{0002}aaa.a\U{0006}"[i] == '.' && |"\U{0008}aaaaa\0aaa\U{0004}\U{0002}aaa.a\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0008}aaaaa\0aaa\U{0004}\U{0002}aaa.a\U{0006}"| && "\U{0008}aaaaa\0aaa\U{0004}\U{0002}aaa.a\U{0006}"[i] == '.' && |"\U{0008}aaaaa\0aaa\U{0004}\U{0002}aaa.a\U{0006}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 17.797305 s

method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaaaaaaaaaaa\U{0002}aaa\0\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaaa\U{0002}aaa\0\U{0004}"| && "\U{0006}aaaaaaaaaaaa\U{0002}aaa\0\U{0004}"[i] == '.' && |"\U{0006}aaaaaaaaaaaa\U{0002}aaa\0\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaaa\U{0002}aaa\0\U{0004}"| && "\U{0006}aaaaaaaaaaaa\U{0002}aaa\0\U{0004}"[i] == '.' && |"\U{0006}aaaaaaaaaaaa\U{0002}aaa\0\U{0004}"| - i - 1 == 2;
}
method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\0a.\U{0002}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\0a.\U{0002}a"| && "\U{0004}\0a.\U{0002}a"[i] == '.' && |"\U{0004}\0a.\U{0002}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\0a.\U{0002}a"| && "\U{0004}\0a.\U{0002}a"[i] == '.' && |"\U{0004}\0a.\U{0002}a"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 19.4236298 s

method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aa\U{0002}\U{0008}a\U{0006}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| && "\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"[i] == '.' && |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| && "\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"[i] == '.' && |"\U{0004}aa\U{0002}\U{0008}a\U{0006}\0"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}aa\U{0001}aaaaa.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| && "\U{0005}aa\U{0001}aaaaa.\U{0003}a"[i] == '.' && |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| && "\U{0005}aa\U{0001}aaaaa.\U{0003}a"[i] == '.' && |"\U{0005}aa\U{0001}aaaaa.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 21.1223855 s

method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaa\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaa\U{0004}\0"| && "\U{0002}aaaa\U{0004}\0"[i] == '.' && |"\U{0002}aaaa\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaa\U{0004}\0"| && "\U{0002}aaaa\U{0004}\0"[i] == '.' && |"\U{0002}aaaa\U{0004}\0"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("\taaaa\U{0001}a\U{0003}a.\U{0005}\U{0007}");
expect r0 ==> exists i :: 0 <= i < |"\taaaa\U{0001}a\U{0003}a.\U{0005}\U{0007}"| && "\taaaa\U{0001}a\U{0003}a.\U{0005}\U{0007}"[i] == '.' && |"\taaaa\U{0001}a\U{0003}a.\U{0005}\U{0007}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\taaaa\U{0001}a\U{0003}a.\U{0005}\U{0007}"| && "\taaaa\U{0001}a\U{0003}a.\U{0005}\U{0007}"[i] == '.' && |"\taaaa\U{0001}a\U{0003}a.\U{0005}\U{0007}"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 22.7678145 s

method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a");
expect r0 ==> exists i :: 0 <= i < |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| && "\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"[i] == '.' && |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| && "\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"[i] == '.' && |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| - i - 1 == 2;
}
method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision(".\0a");
expect r0 ==> exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 24.5347576 s

method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0002}\0"| && "aa\U{0002}\0"[i] == '.' && |"aa\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0002}\0"| && "aa\U{0002}\0"[i] == '.' && |"aa\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test29() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}.aa"| && "\U{0001}.aa"[i] == '.' && |"\U{0001}.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}.aa"| && "\U{0001}.aa"[i] == '.' && |"\U{0001}.aa"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 26.2821129 s

method {:test} Test30() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}a\0\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}a\0\U{0002}\U{0004}"| && "\U{0006}a\0\U{0002}\U{0004}"[i] == '.' && |"\U{0006}a\0\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}a\0\U{0002}\U{0004}"| && "\U{0006}a\0\U{0002}\U{0004}"[i] == '.' && |"\U{0006}a\0\U{0002}\U{0004}"| - i - 1 == 2;
}
method {:test} Test31() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| && "aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"[i] == '.' && |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| && "aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"[i] == '.' && |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 27.7531612 s

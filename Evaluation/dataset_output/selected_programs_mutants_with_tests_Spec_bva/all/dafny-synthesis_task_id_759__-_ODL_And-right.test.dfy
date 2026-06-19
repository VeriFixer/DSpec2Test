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
    if s[i] == '.' {
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

// REPEAT 1 - TIME: 9.8612415 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\0a");
expect r0 ==> exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0007}\U{0001}aa\U{0003}aaaaaa.a\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0007}\U{0001}aa\U{0003}aaaaaa.a\U{0005}"| && "\U{0007}\U{0001}aa\U{0003}aaaaaa.a\U{0005}"[i] == '.' && |"\U{0007}\U{0001}aa\U{0003}aaaaaa.a\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0007}\U{0001}aa\U{0003}aaaaaa.a\U{0005}"| && "\U{0007}\U{0001}aa\U{0003}aaaaaa.a\U{0005}"[i] == '.' && |"\U{0007}\U{0001}aa\U{0003}aaaaaa.a\U{0005}"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 10.9064898 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaa\0aaaaaaaa\U{0004}\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaa\0aaaaaaaa\U{0004}\U{0006}"| && "\U{0002}aaa\0aaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\U{0002}aaa\0aaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaa\0aaaaaaaa\U{0004}\U{0006}"| && "\U{0002}aaa\0aaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\U{0002}aaa\0aaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}\U{0001}aaaaaaaaaaa\U{0005}\U{0007}aaa.a\t");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}\U{0007}aaa.a\t"| && "\U{0003}\U{0001}aaaaaaaaaaa\U{0005}\U{0007}aaa.a\t"[i] == '.' && |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}\U{0007}aaa.a\t"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}\U{0007}aaa.a\t"| && "\U{0003}\U{0001}aaaaaaaaaaa\U{0005}\U{0007}aaa.a\t"[i] == '.' && |"\U{0003}\U{0001}aaaaaaaaaaa\U{0005}\U{0007}aaa.a\t"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 12.023929 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}a\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}a\0"| && "\U{0002}a\0"[i] == '.' && |"\U{0002}a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}a\0"| && "\U{0002}a\0"[i] == '.' && |"\U{0002}a\0"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| && "\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"[i] == '.' && |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| && "\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"[i] == '.' && |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 13.2367094 s

method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}"| && "\0aaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}"[i] == '.' && |"\0aaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}"| && "\0aaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}"[i] == '.' && |"\0aaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}"| - i - 1 == 2;
}
method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaaa\0aaaaaa.\U{0002}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaaa\0aaaaaa.\U{0002}a"| && "\U{0004}aaaaa\0aaaaaa.\U{0002}a"[i] == '.' && |"\U{0004}aaaaa\0aaaaaa.\U{0002}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaaa\0aaaaaa.\U{0002}a"| && "\U{0004}aaaaa\0aaaaaa.\U{0002}a"[i] == '.' && |"\U{0004}aaaaa\0aaaaaa.\U{0002}a"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 14.259175 s

method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaa\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| && "\0aaaaaaaaaaaa\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| && "\0aaaaaaaaaaaa\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaaaaaaaa\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}");
expect r0 ==> exists i :: 0 <= i < |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| && "\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"[i] == '.' && |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| && "\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"[i] == '.' && |"\taaaaaaaa\U{0001}a\U{0003}.\U{0005}\U{0007}"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 15.2142367 s

method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("\0a");
expect r0 ==> exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| && "\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"[i] == '.' && |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| && "\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"[i] == '.' && |"\U{0001}aaaaaaaaaaa\U{0003}\U{0005}a.\U{0007}\t"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 16.4058155 s

method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| && "\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"[i] == '.' && |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| && "\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"[i] == '.' && |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| - i - 1 == 2;
}
method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| && "\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"[i] == '.' && |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| && "\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"[i] == '.' && |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 17.5060214 s

method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| && "\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"[i] == '.' && |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| && "\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"[i] == '.' && |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| - i - 1 == 2;
}
method {:test} Test29() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| && "\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"[i] == '.' && |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| && "\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"[i] == '.' && |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 18.6935908 s

method {:test} Test30() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaaaaaaaaaaaa\U{0002}aa\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaaaa\U{0002}aa\U{0004}\0"| && "\U{0006}aaaaaaaaaaaaa\U{0002}aa\U{0004}\0"[i] == '.' && |"\U{0006}aaaaaaaaaaaaa\U{0002}aa\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaaaa\U{0002}aa\U{0004}\0"| && "\U{0006}aaaaaaaaaaaaa\U{0002}aa\U{0004}\0"[i] == '.' && |"\U{0006}aaaaaaaaaaaaa\U{0002}aa\U{0004}\0"| - i - 1 == 2;
}
method {:test} Test31() {
var r0 := IsDecimalWithTwoPrecision("\U{000B}aaaaaaaaaaaaaa\U{0005}aa\U{0003}a\U{0007}.\t\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"\U{000B}aaaaaaaaaaaaaa\U{0005}aa\U{0003}a\U{0007}.\t\U{0001}"| && "\U{000B}aaaaaaaaaaaaaa\U{0005}aa\U{0003}a\U{0007}.\t\U{0001}"[i] == '.' && |"\U{000B}aaaaaaaaaaaaaa\U{0005}aa\U{0003}a\U{0007}.\t\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000B}aaaaaaaaaaaaaa\U{0005}aa\U{0003}a\U{0007}.\t\U{0001}"| && "\U{000B}aaaaaaaaaaaaaa\U{0005}aa\U{0003}a\U{0007}.\t\U{0001}"[i] == '.' && |"\U{000B}aaaaaaaaaaaaaa\U{0005}aa\U{0003}a\U{0007}.\t\U{0001}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 19.9414128 s

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
    break;
    if s[i] == '.' && |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}


method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2)
    {
        if s[i] == '.' && |s| - i - 1 == 2 {
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
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa.aa"| && "aaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa.aa"| && "aaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 9.0802901 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaa\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaa\U{0002}\0"| && "aaaaaaaaaaa\U{0002}\0"[i] == '.' && |"aaaaaaaaaaa\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaa\U{0002}\0"| && "aaaaaaaaaaa\U{0002}\0"[i] == '.' && |"aaaaaaaaaaa\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| && "\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"[i] == '.' && |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| && "\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"[i] == '.' && |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 10.0310738 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| && "\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"[i] == '.' && |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| && "\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"[i] == '.' && |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}\U{0001}.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 11.1470841 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && "\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] == '.' && |"\naa\0a\U{0004}aaaaaa\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}");
expect r0 ==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| && "\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| && "\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa.\U{0005}\U{0003}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 12.492818 s

method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| && "aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"[i] == '.' && |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| && "aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"[i] == '.' && |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| - i - 1 == 2;
}
method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaa.a\U{0001}"| && "\U{0003}aaaaa.a\U{0001}"[i] == '.' && |"\U{0003}aaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaa.a\U{0001}"| && "\U{0003}aaaaa.a\U{0001}"[i] == '.' && |"\U{0003}aaaaa.a\U{0001}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 14.0099898 s

method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n");
expect r0 ==> exists i :: 0 <= i < |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| && "a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"[i] == '.' && |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| && "a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"[i] == '.' && |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| && "aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"[i] == '.' && |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| && "aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"[i] == '.' && |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 15.1567589 s

method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| && "aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"[i] == '.' && |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| && "aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"[i] == '.' && |"aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0006}aaaaaaa\U{0008}a\naa\0\U{0004}\U{000C}"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| && "aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"[i] == '.' && |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| && "aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"[i] == '.' && |"aaaaaaaaa\U{0001}aaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0007}\t\U{0003}aa.a\U{000B}"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 16.3522854 s

method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| && "aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"[i] == '.' && |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| && "aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"[i] == '.' && |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| - i - 1 == 2;
}
method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}.\U{0001}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}.\U{0001}\U{0005}"| && "\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}.\U{0001}\U{0005}"| && "\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 17.8185956 s

method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}\U{0004}"| - i - 1 == 2;
}
method {:test} Test29() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| && "aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"[i] == '.' && |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| && "aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"[i] == '.' && |"aaaaaaaaaaaaa\U{0006}aaaaaa\0aaaaaaaaaa\U{0004}aaaaaaaaaa\U{0002}\U{0008}a.a\n"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 19.253268 s

method {:test} Test30() {
var r0 := IsDecimalWithTwoPrecision("aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| && "aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"[i] == '.' && |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| && "aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"[i] == '.' && |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| - i - 1 == 2;
}
method {:test} Test31() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| && "aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"[i] == '.' && |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| && "aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"[i] == '.' && |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 20.5670489 s

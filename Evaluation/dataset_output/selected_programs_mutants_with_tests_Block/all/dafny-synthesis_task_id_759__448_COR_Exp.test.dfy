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
    if s[i] == '.' <== |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaa\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaa\0"| && "aaaaaaaa\0"[i] == '.' && |"aaaaaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaa\0"| && "aaaaaaaa\0"[i] == '.' && |"aaaaaaaa\0"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 2.6469102 s

method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaa.aa"| && "\U{0001}aaa.aa"[i] == '.' && |"\U{0001}aaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaa.aa"| && "\U{0001}aaa.aa"[i] == '.' && |"\U{0001}aaa.aa"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\0"| && "aaaaa\0"[i] == '.' && |"aaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\0"| && "aaaaa\0"[i] == '.' && |"aaaaa\0"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 4.1491531 s

method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision(".\0a");
expect r0 ==> exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("a\U{0002}\0\U{0004}a");
expect r0 ==> exists i :: 0 <= i < |"a\U{0002}\0\U{0004}a"| && "a\U{0002}\0\U{0004}a"[i] == '.' && |"a\U{0002}\0\U{0004}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\U{0002}\0\U{0004}a"| && "a\U{0002}\0\U{0004}a"[i] == '.' && |"a\U{0002}\0\U{0004}a"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 5.8457538 s

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("\0.\U{0002}a");
expect r0 ==> exists i :: 0 <= i < |"\0.\U{0002}a"| && "\0.\U{0002}a"[i] == '.' && |"\0.\U{0002}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0.\U{0002}a"| && "\0.\U{0002}a"[i] == '.' && |"\0.\U{0002}a"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aa\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aa\0"| && "\U{0002}aa\0"[i] == '.' && |"\U{0002}aa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aa\0"| && "\U{0002}aa\0"[i] == '.' && |"\U{0002}aa\0"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 7.4392952 s

method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaa.\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaa.\0\U{0002}"| && "\U{0004}aaa.\0\U{0002}"[i] == '.' && |"\U{0004}aaa.\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaa.\0\U{0002}"| && "\U{0004}aaa.\0\U{0002}"[i] == '.' && |"\U{0004}aaa.\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\0a\U{0002}aa");
expect r0 ==> exists i :: 0 <= i < |"\0a\U{0002}aa"| && "\0a\U{0002}aa"[i] == '.' && |"\0a\U{0002}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a\U{0002}aa"| && "\0a\U{0002}aa"[i] == '.' && |"\0a\U{0002}aa"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 8.8188752 s

method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| && "\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"[i] == '.' && |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| && "\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"[i] == '.' && |"\U{0004}aaaaaaaa\0aaaaaaa.\U{0002}\U{0006}"| - i - 1 == 2;
}
method {:test} Test11() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaa\0aa"| && "\U{0002}aaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaa\0aa"| && "\U{0002}aaaaaaa\0aa"[i] == '.' && |"\U{0002}aaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 9.6668811 s

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("aaaaa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaa.\U{0002}\0"| && "aaaaa.\U{0002}\0"[i] == '.' && |"aaaaa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa.\U{0002}\0"| && "aaaaa.\U{0002}\0"[i] == '.' && |"aaaaa.\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("a\0");
expect r0 ==> exists i :: 0 <= i < |"a\0"| && "a\0"[i] == '.' && |"a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\0"| && "a\0"[i] == '.' && |"a\0"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 10.6658397 s

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aa.\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aa.\0\U{0002}"| && "\U{0004}aa.\0\U{0002}"[i] == '.' && |"\U{0004}aa.\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aa.\0\U{0002}"| && "\U{0004}aa.\0\U{0002}"[i] == '.' && |"\U{0004}aa.\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}");
expect r0 ==> exists i :: 0 <= i < |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| && "\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"[i] == '.' && |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| && "\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"[i] == '.' && |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 11.6667513 s

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaa.\U{0002}\0"| && "aaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaa.\U{0002}\0"| && "aaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaa.\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 12.4932641 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| && "aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"[i] == '.' && |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| && "aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"[i] == '.' && |"aaaaa\0a\U{0006}\U{0004}\U{0008}a\naaaa\U{000C}a.\U{0002}\U{000E}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0aa"| && "\U{0002}\0aa"[i] == '.' && |"\U{0002}\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0aa"| && "\U{0002}\0aa"[i] == '.' && |"\U{0002}\0aa"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 13.5378856 s

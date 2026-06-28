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
var r0 := IsDecimalWithTwoPrecision("a");
expect r0 ==> exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaa.aa"| && "aaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 23.8892387 s

method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("\0a");
expect r0 ==> exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a"| && "\0a"[i] == '.' && |"\0a"| - i - 1 == 2;
}
method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa.a\U{0001}"| && "aaaaaaaaaaaaaaaa.a\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa.a\U{0001}"| && "aaaaaaaaaaaaaaaa.a\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaa.a\U{0001}"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision(".\U{0001}a");
expect r0 ==> exists i :: 0 <= i < |".\U{0001}a"| && ".\U{0001}a"[i] == '.' && |".\U{0001}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\U{0001}a"| && ".\U{0001}a"[i] == '.' && |".\U{0001}a"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 47.2170224 s

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aa\0\U{0002}aaaaaaaaaaaaa\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aa\0\U{0002}aaaaaaaaaaaaa\U{0006}"| && "\U{0004}aa\0\U{0002}aaaaaaaaaaaaa\U{0006}"[i] == '.' && |"\U{0004}aa\0\U{0002}aaaaaaaaaaaaa\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aa\0\U{0002}aaaaaaaaaaaaa\U{0006}"| && "\U{0004}aa\0\U{0002}aaaaaaaaaaaaa\U{0006}"[i] == '.' && |"\U{0004}aa\0\U{0002}aaaaaaaaaaaaa\U{0006}"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaa.a\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaa.a\0"| && "\U{0002}aaaaaaaaaa.a\0"[i] == '.' && |"\U{0002}aaaaaaaaaa.a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaa.a\0"| && "\U{0002}aaaaaaaaaa.a\0"[i] == '.' && |"\U{0002}aaaaaaaaaa.a\0"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 80.0551193 s

method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| && "\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"[i] == '.' && |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| && "\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"[i] == '.' && |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| - i - 1 == 2;
}
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}\U{0005}.\U{0001}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}\U{0005}.\U{0001}a"| && "\U{0003}\U{0005}.\U{0001}a"[i] == '.' && |"\U{0003}\U{0005}.\U{0001}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}\U{0005}.\U{0001}a"| && "\U{0003}\U{0005}.\U{0001}a"[i] == '.' && |"\U{0003}\U{0005}.\U{0001}a"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 114.2840015 s

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}a\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}a\0\U{0002}"| && "\U{0004}a\0\U{0002}"[i] == '.' && |"\U{0004}a\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}a\0\U{0002}"| && "\U{0004}a\0\U{0002}"[i] == '.' && |"\U{0004}a\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa\0aa.\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| && "aaaaaaaaa\0aa.\U{0004}\U{0002}"[i] == '.' && |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| && "aaaaaaaaa\0aa.\U{0004}\U{0002}"[i] == '.' && |"aaaaaaaaa\0aa.\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\0aaaaaa.\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| && "aaaaa\0aaaaaa.\U{0004}\U{0002}"[i] == '.' && |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| && "aaaaa\0aaaaaa.\U{0004}\U{0002}"[i] == '.' && |"aaaaa\0aaaaaa.\U{0004}\U{0002}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 151.2060275 s

method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}"| && "\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}"[i] == '.' && |"\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}"| && "\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}"[i] == '.' && |"\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaa\0a.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaa\0a.aa"| && "\U{0002}aaaaa\0a.aa"[i] == '.' && |"\U{0002}aaaaa\0a.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaa\0a.aa"| && "\U{0002}aaaaa\0a.aa"[i] == '.' && |"\U{0002}aaaaa\0a.aa"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaa.\0a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaa.\0a"| && "\U{0002}aaaa.\0a"[i] == '.' && |"\U{0002}aaaa.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaa.\0a"| && "\U{0002}aaaa.\0a"[i] == '.' && |"\U{0002}aaaa.\0a"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 195.9784175 s

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}a\0a\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}a\0a\U{0004}\U{0002}"| && "\U{0006}a\0a\U{0004}\U{0002}"[i] == '.' && |"\U{0006}a\0a\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}a\0a\U{0004}\U{0002}"| && "\U{0006}a\0a\U{0004}\U{0002}"[i] == '.' && |"\U{0006}a\0a\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| && "aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"[i] == '.' && |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| && "aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"[i] == '.' && |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| - i - 1 == 2;
}
method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| && "aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"[i] == '.' && |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| && "aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"[i] == '.' && |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 248.0897013 s

method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaa\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaa\0"| && "\U{0002}aaaaa\0"[i] == '.' && |"\U{0002}aaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaa\0"| && "\U{0002}aaaaa\0"[i] == '.' && |"\U{0002}aaaaa\0"| - i - 1 == 2;
}
method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaa\U{0002}aa.\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0002}aa.\U{0004}\0"| && "aaaaaaaaaaaaaaaa\U{0002}aa.\U{0004}\0"[i] == '.' && |"aaaaaaaaaaaaaaaa\U{0002}aa.\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0002}aa.\U{0004}\0"| && "aaaaaaaaaaaaaaaa\U{0002}aa.\U{0004}\0"[i] == '.' && |"aaaaaaaaaaaaaaaa\U{0002}aa.\U{0004}\0"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 296.0114154 s

method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaa\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaa\U{0004}\0"| && "\U{0002}aaa\U{0004}\0"[i] == '.' && |"\U{0002}aaa\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaa\U{0004}\0"| && "\U{0002}aaa\U{0004}\0"[i] == '.' && |"\U{0002}aaa\U{0004}\0"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaa.a\U{0001}"| && "aaaaaaa.a\U{0001}"[i] == '.' && |"aaaaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaa.a\U{0001}"| && "aaaaaaa.a\U{0001}"[i] == '.' && |"aaaaaaa.a\U{0001}"| - i - 1 == 2;
}
method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("aaaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaa.a\U{0001}"| && "aaaaaa.a\U{0001}"[i] == '.' && |"aaaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaa.a\U{0001}"| && "aaaaaa.a\U{0001}"[i] == '.' && |"aaaaaa.a\U{0001}"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 358.5306782 s

method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| && "\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"[i] == '.' && |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| && "\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"[i] == '.' && |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 412.1149416 s

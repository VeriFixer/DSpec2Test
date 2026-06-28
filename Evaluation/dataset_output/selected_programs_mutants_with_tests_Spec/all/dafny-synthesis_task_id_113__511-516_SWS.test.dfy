// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if |s| == 0 {
    result := false;
  } else {
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result <==> forall k :: 0 <= k < i ==> IsDigit(s[k])
    {
      if !IsDigit(s[i]) {
        break;
        result := false;
      }
    }
  }
}


method {:test} Test0() {
var r0 := IsInteger("");
expect r0 <==> |""| > 0 && forall i :: 0 <= i < |""| ==> IsDigit(""[i]);
}
method {:test} Test1() {
var r0 := IsInteger("a");
expect r0 <==> |"a"| > 0 && forall i :: 0 <= i < |"a"| ==> IsDigit("a"[i]);
}
method {:test} Test2() {
var r0 := IsInteger("/");
expect r0 <==> |"/"| > 0 && forall i :: 0 <= i < |"/"| ==> IsDigit("/"[i]);
}

// REPEAT 1 - TIME: 4.5074394 s

method {:test} Test3() {
var r0 := IsInteger("a0");
expect r0 <==> |"a0"| > 0 && forall i :: 0 <= i < |"a0"| ==> IsDigit("a0"[i]);
}
method {:test} Test4() {
var r0 := IsInteger("\U{0008}\0");
expect r0 <==> |"\U{0008}\0"| > 0 && forall i :: 0 <= i < |"\U{0008}\0"| ==> IsDigit("\U{0008}\0"[i]);
}

// REPEAT 2 - TIME: 6.5337085 s

method {:test} Test5() {
var r0 := IsInteger("aaaaaaaaaa7a1");
expect r0 <==> |"aaaaaaaaaa7a1"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaa7a1"| ==> IsDigit("aaaaaaaaaa7a1"[i]);
}
method {:test} Test6() {
var r0 := IsInteger("\U{0001}\0\U{0019}");
expect r0 <==> |"\U{0001}\0\U{0019}"| > 0 && forall i :: 0 <= i < |"\U{0001}\0\U{0019}"| ==> IsDigit("\U{0001}\0\U{0019}"[i]);
}

// REPEAT 3 - TIME: 8.6611614 s

method {:test} Test7() {
var r0 := IsInteger("4aa24aaaaaaaa4");
expect r0 <==> |"4aa24aaaaaaaa4"| > 0 && forall i :: 0 <= i < |"4aa24aaaaaaaa4"| ==> IsDigit("4aa24aaaaaaaa4"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> |"\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"| > 0 && forall i :: 0 <= i < |"\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"| ==> IsDigit("\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i]);
}

// REPEAT 4 - TIME: 10.7133145 s

method {:test} Test9() {
var r0 := IsInteger("21aaaaaaaaaaaaaaaaaa2");
expect r0 <==> |"21aaaaaaaaaaaaaaaaaa2"| > 0 && forall i :: 0 <= i < |"21aaaaaaaaaaaaaaaaaa2"| ==> IsDigit("21aaaaaaaaaaaaaaaaaa2"[i]);
}
method {:test} Test10() {
var r0 := IsInteger("\0a\U{0008}a");
expect r0 <==> |"\0a\U{0008}a"| > 0 && forall i :: 0 <= i < |"\0a\U{0008}a"| ==> IsDigit("\0a\U{0008}a"[i]);
}

// REPEAT 5 - TIME: 12.4035515 s

method {:test} Test11() {
var r0 := IsInteger("3aaa4");
expect r0 <==> |"3aaa4"| > 0 && forall i :: 0 <= i < |"3aaa4"| ==> IsDigit("3aaa4"[i]);
}
method {:test} Test12() {
var r0 := IsInteger("\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}");
expect r0 <==> |"\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}"| > 0 && forall i :: 0 <= i < |"\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}"| ==> IsDigit("\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}"[i]);
}

// REPEAT 6 - TIME: 14.0993132 s

method {:test} Test13() {
var r0 := IsInteger("2aaaa6aaa97a748");
expect r0 <==> |"2aaaa6aaa97a748"| > 0 && forall i :: 0 <= i < |"2aaaa6aaa97a748"| ==> IsDigit("2aaaa6aaa97a748"[i]);
}
method {:test} Test14() {
var r0 := IsInteger("\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa");
expect r0 <==> |"\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa"| > 0 && forall i :: 0 <= i < |"\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa"| ==> IsDigit("\U{0006}aaaa\0\U{0005}aaaaaaaa\U{0004}\U{0008}\U{0002}\U{0003}\U{0001}aa"[i]);
}

// REPEAT 7 - TIME: 15.7531055 s

method {:test} Test15() {
var r0 := IsInteger("9aaaaaa1aaaaa422");
expect r0 <==> |"9aaaaaa1aaaaa422"| > 0 && forall i :: 0 <= i < |"9aaaaaa1aaaaa422"| ==> IsDigit("9aaaaaa1aaaaa422"[i]);
}
method {:test} Test16() {
var r0 := IsInteger("\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}");
expect r0 <==> |"\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}"| > 0 && forall i :: 0 <= i < |"\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}"| ==> IsDigit("\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}"[i]);
}

// REPEAT 8 - TIME: 17.4371422 s

method {:test} Test17() {
var r0 := IsInteger("7aaaaaaaaaaa9aaaa76aaaaaaa");
expect r0 <==> |"7aaaaaaaaaaa9aaaa76aaaaaaa"| > 0 && forall i :: 0 <= i < |"7aaaaaaaaaaa9aaaa76aaaaaaa"| ==> IsDigit("7aaaaaaaaaaa9aaaa76aaaaaaa"[i]);
}
method {:test} Test18() {
var r0 := IsInteger("\U{0001}a\U{0018}aa\0");
expect r0 <==> |"\U{0001}a\U{0018}aa\0"| > 0 && forall i :: 0 <= i < |"\U{0001}a\U{0018}aa\0"| ==> IsDigit("\U{0001}a\U{0018}aa\0"[i]);
}

// REPEAT 9 - TIME: 19.2909107 s

method {:test} Test19() {
var r0 := IsInteger("2aaaaaaaaaaaa7826aaa499aaa4");
expect r0 <==> |"2aaaaaaaaaaaa7826aaa499aaa4"| > 0 && forall i :: 0 <= i < |"2aaaaaaaaaaaa7826aaa499aaa4"| ==> IsDigit("2aaaaaaaaaaaa7826aaa499aaa4"[i]);
}
method {:test} Test20() {
var r0 := IsInteger("\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}");
expect r0 <==> |"\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}"| > 0 && forall i :: 0 <= i < |"\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}"| ==> IsDigit("\U{0001}aaaaaaaaaa\0a\U{0005}a\"\U{0002}aa\U{0003}\U{0004}\U{0006}\U{0007}"[i]);
}

// REPEAT 10 - TIME: 21.1062192 s

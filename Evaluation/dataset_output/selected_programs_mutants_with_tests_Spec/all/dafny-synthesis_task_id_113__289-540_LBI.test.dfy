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
      break;
      if !IsDigit(s[i]) {
        result := false;
        break;
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

// REPEAT 1 - TIME: 4.4769834 s

method {:test} Test3() {
var r0 := IsInteger("a1");
expect r0 <==> |"a1"| > 0 && forall i :: 0 <= i < |"a1"| ==> IsDigit("a1"[i]);
}
method {:test} Test4() {
var r0 := IsInteger("\U{0008}\0");
expect r0 <==> |"\U{0008}\0"| > 0 && forall i :: 0 <= i < |"\U{0008}\0"| ==> IsDigit("\U{0008}\0"[i]);
}

// REPEAT 2 - TIME: 6.547058 s

method {:test} Test5() {
var r0 := IsInteger("a01");
expect r0 <==> |"a01"| > 0 && forall i :: 0 <= i < |"a01"| ==> IsDigit("a01"[i]);
}
method {:test} Test6() {
var r0 := IsInteger("\U{0002}\0\U{0008}aaaaaaaaaaaaa\U{0001}");
expect r0 <==> |"\U{0002}\0\U{0008}aaaaaaaaaaaaa\U{0001}"| > 0 && forall i :: 0 <= i < |"\U{0002}\0\U{0008}aaaaaaaaaaaaa\U{0001}"| ==> IsDigit("\U{0002}\0\U{0008}aaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 8.4210734 s

method {:test} Test7() {
var r0 := IsInteger("2a1");
expect r0 <==> |"2a1"| > 0 && forall i :: 0 <= i < |"2a1"| ==> IsDigit("2a1"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}");
expect r0 <==> |"\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}"| ==> IsDigit("\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}"[i]);
}

// REPEAT 4 - TIME: 10.0443884 s

method {:test} Test9() {
var r0 := IsInteger("4a4aaa2aaaaaaaa4");
expect r0 <==> |"4a4aaa2aaaaaaaa4"| > 0 && forall i :: 0 <= i < |"4a4aaa2aaaaaaaa4"| ==> IsDigit("4a4aaa2aaaaaaaa4"[i]);
}
method {:test} Test10() {
var r0 := IsInteger("\U{0001}\0\U{0008}a");
expect r0 <==> |"\U{0001}\0\U{0008}a"| > 0 && forall i :: 0 <= i < |"\U{0001}\0\U{0008}a"| ==> IsDigit("\U{0001}\0\U{0008}a"[i]);
}

// REPEAT 5 - TIME: 11.550057 s

method {:test} Test11() {
var r0 := IsInteger("5a42aaaaa2aaaaaaaaa");
expect r0 <==> |"5a42aaaaa2aaaaaaaaa"| > 0 && forall i :: 0 <= i < |"5a42aaaaa2aaaaaaaaa"| ==> IsDigit("5a42aaaaa2aaaaaaaaa"[i]);
}
method {:test} Test12() {
var r0 := IsInteger("\U{0001}a\0\U{0018}\U{0002}");
expect r0 <==> |"\U{0001}a\0\U{0018}\U{0002}"| > 0 && forall i :: 0 <= i < |"\U{0001}a\0\U{0018}\U{0002}"| ==> IsDigit("\U{0001}a\0\U{0018}\U{0002}"[i]);
}

// REPEAT 6 - TIME: 13.5241505 s

method {:test} Test13() {
var r0 := IsInteger("aaaaa4aaaaaaaa2a2441");
expect r0 <==> |"aaaaa4aaaaaaaa2a2441"| > 0 && forall i :: 0 <= i < |"aaaaa4aaaaaaaa2a2441"| ==> IsDigit("aaaaa4aaaaaaaa2a2441"[i]);
}
method {:test} Test14() {
var r0 := IsInteger("aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a");
expect r0 <==> |"aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a"| > 0 && forall i :: 0 <= i < |"aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a"| ==> IsDigit("aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a"[i]);
}

// REPEAT 7 - TIME: 15.2601795 s

method {:test} Test15() {
var r0 := IsInteger("aa4aa4aaaaaaaaaa97268aaaaaa7");
expect r0 <==> |"aa4aa4aaaaaaaaaa97268aaaaaa7"| > 0 && forall i :: 0 <= i < |"aa4aa4aaaaaaaaaa97268aaaaaa7"| ==> IsDigit("aa4aa4aaaaaaaaaa97268aaaaaa7"[i]);
}
method {:test} Test16() {
var r0 := IsInteger("\0a\U{0008}a\U{0002}\U{0001}");
expect r0 <==> |"\0a\U{0008}a\U{0002}\U{0001}"| > 0 && forall i :: 0 <= i < |"\0a\U{0008}a\U{0002}\U{0001}"| ==> IsDigit("\0a\U{0008}a\U{0002}\U{0001}"[i]);
}

// REPEAT 8 - TIME: 16.9296233 s

method {:test} Test17() {
var r0 := IsInteger("4aa474a7aaaaaaaa828aa");
expect r0 <==> |"4aa474a7aaaaaaaa828aa"| > 0 && forall i :: 0 <= i < |"4aa474a7aaaaaaaa828aa"| ==> IsDigit("4aa474a7aaaaaaaa828aa"[i]);
}
method {:test} Test18() {
var r0 := IsInteger("\U{0001}aa\U{0019}aa\0");
expect r0 <==> |"\U{0001}aa\U{0019}aa\0"| > 0 && forall i :: 0 <= i < |"\U{0001}aa\U{0019}aa\0"| ==> IsDigit("\U{0001}aa\U{0019}aa\0"[i]);
}

// REPEAT 9 - TIME: 18.5012359 s

method {:test} Test19() {
var r0 := IsInteger("aaa76978aaaaaaaa28442a");
expect r0 <==> |"aaa76978aaaaaaaa28442a"| > 0 && forall i :: 0 <= i < |"aaa76978aaaaaaaa28442a"| ==> IsDigit("aaa76978aaaaaaaa28442a"[i]);
}
method {:test} Test20() {
var r0 := IsInteger("\U{0003}aa\U{0001}\U{0002}\0\U{0008}a");
expect r0 <==> |"\U{0003}aa\U{0001}\U{0002}\0\U{0008}a"| > 0 && forall i :: 0 <= i < |"\U{0003}aa\U{0001}\U{0002}\0\U{0008}a"| ==> IsDigit("\U{0003}aa\U{0001}\U{0002}\0\U{0008}a"[i]);
}

// REPEAT 10 - TIME: 19.9993202 s

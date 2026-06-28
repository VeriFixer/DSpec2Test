// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if |s| > 0 {
    result := false;
  } else {
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result <==> forall k :: 0 <= k < i ==> IsDigit(s[k])
    {
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
var r0 := IsInteger("aaaaaaaa/");
expect r0 <==> |"aaaaaaaa/"| > 0 && forall i :: 0 <= i < |"aaaaaaaa/"| ==> IsDigit("aaaaaaaa/"[i]);
}

// REPEAT 1 - TIME: 19.1288197 s

method {:test} Test3() {
var r0 := IsInteger("01");
expect r0 <==> |"01"| > 0 && forall i :: 0 <= i < |"01"| ==> IsDigit("01"[i]);
}
method {:test} Test4() {
var r0 := IsInteger("\U{0019}\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}");
expect r0 <==> |"\U{0019}\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0019}\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}"| ==> IsDigit("\U{0019}\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 2 - TIME: 35.861901 s

method {:test} Test5() {
var r0 := IsInteger("aa2aa4aaa4aaaaaaaaaaaaa");
expect r0 <==> |"aa2aa4aaa4aaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aa2aa4aaa4aaaaaaaaaaaaa"| ==> IsDigit("aa2aa4aaa4aaaaaaaaaaaaa"[i]);
}
method {:test} Test6() {
var r0 := IsInteger("\U{0008}a\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}");
expect r0 <==> |"\U{0008}a\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0008}a\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}"| ==> IsDigit("\U{0008}a\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 3 - TIME: 54.5134192 s

method {:test} Test7() {
var r0 := IsInteger("aa7aaaaaaaaaaaaaaaaaaaa6aa8a");
expect r0 <==> |"aa7aaaaaaaaaaaaaaaaaaaa6aa8a"| > 0 && forall i :: 0 <= i < |"aa7aaaaaaaaaaaaaaaaaaaa6aa8a"| ==> IsDigit("aa7aaaaaaaaaaaaaaaaaaaa6aa8a"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("aaaaaaaaaaaaa\U{0008}aaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaa\U{0008}aaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaa\U{0008}aaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaa\U{0008}aaaaaaaaaaaa"[i]);
}

// REPEAT 4 - TIME: 75.4019431 s

method {:test} Test9() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaaaaaa4aaa24");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaa4aaa24"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa4aaa24"| ==> IsDigit("aaaaaaaaaaaaaaaaaaaaaaa4aaa24"[i]);
}
method {:test} Test10() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaa\U{0008}aaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaa\U{0008}aaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa\U{0008}aaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaaaaa\U{0008}aaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 95.9987475 s

method {:test} Test11() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaaaaaa1aaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaa1aaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa1aaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaaaaaaaaa1aaaaaa"[i]);
}
method {:test} Test12() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 6 - TIME: 116.1856586 s

method {:test} Test13() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test14() {
var r0 := IsInteger("aaaaaaaaaaaaaaa\U{0008}aaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaa\U{0008}aaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaa\U{0008}aaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaa\U{0008}aaaaaaaaaaa"[i]);
}

// REPEAT 7 - TIME: 139.9188732 s

method {:test} Test15() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test16() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaaaa\U{0008}");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaa\U{0008}"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaa\U{0008}"| ==> IsDigit("aaaaaaaaaaaaaaaaaaaaa\U{0008}"[i]);
}

// REPEAT 8 - TIME: 167.4315721 s

method {:test} Test17() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test18() {
var r0 := IsInteger("aaaaaaaaaaaa\U{0019}aaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaa\U{0019}aaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaa\U{0019}aaaaaaaa"| ==> IsDigit("aaaaaaaaaaaa\U{0019}aaaaaaaa"[i]);
}

// REPEAT 9 - TIME: 204.0682035 s

method {:test} Test19() {
var r0 := IsInteger("0aaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"0aaaaaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"0aaaaaaaaaaaaaaaaaaa"| ==> IsDigit("0aaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test20() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaaaa\U{0019}");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaa\U{0019}"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa\U{0019}"| ==> IsDigit("aaaaaaaaaaaaaaaaaaa\U{0019}"[i]);
}

// REPEAT 10 - TIME: 243.6164352 s

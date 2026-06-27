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
var r0 := IsInteger("aaaaaaaa/");
expect r0 <==> |"aaaaaaaa/"| > 0 && forall i :: 0 <= i < |"aaaaaaaa/"| ==> IsDigit("aaaaaaaa/"[i]);
}

// REPEAT 1 - TIME: 17.6930018 s

method {:test} Test3() {
var r0 := IsInteger("a1");
expect r0 <==> |"a1"| > 0 && forall i :: 0 <= i < |"a1"| ==> IsDigit("a1"[i]);
}
method {:test} Test4() {
var r0 := IsInteger("\U{0019}\U{0001}aaaaaaaa\U{0003}");
expect r0 <==> |"\U{0019}\U{0001}aaaaaaaa\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0019}\U{0001}aaaaaaaa\U{0003}"| ==> IsDigit("\U{0019}\U{0001}aaaaaaaa\U{0003}"[i]);
}

// REPEAT 2 - TIME: 33.7389947 s

method {:test} Test5() {
var r0 := IsInteger("4a4a");
expect r0 <==> |"4a4a"| > 0 && forall i :: 0 <= i < |"4a4a"| ==> IsDigit("4a4a"[i]);
}
method {:test} Test6() {
var r0 := IsInteger("aa\U{0008}");
expect r0 <==> |"aa\U{0008}"| > 0 && forall i :: 0 <= i < |"aa\U{0008}"| ==> IsDigit("aa\U{0008}"[i]);
}

// REPEAT 3 - TIME: 50.2921467 s

method {:test} Test7() {
var r0 := IsInteger("5aaaa4");
expect r0 <==> |"5aaaa4"| > 0 && forall i :: 0 <= i < |"5aaaa4"| ==> IsDigit("5aaaa4"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("aaaaaaaaa\U{0008}aa");
expect r0 <==> |"aaaaaaaaa\U{0008}aa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaa\U{0008}aa"| ==> IsDigit("aaaaaaaaa\U{0008}aa"[i]);
}

// REPEAT 4 - TIME: 68.088361 s

method {:test} Test9() {
var r0 := IsInteger("9aaa9");
expect r0 <==> |"9aaa9"| > 0 && forall i :: 0 <= i < |"9aaa9"| ==> IsDigit("9aaa9"[i]);
}
method {:test} Test10() {
var r0 := IsInteger("aaaaaaaa\U{0019}aa\0a");
expect r0 <==> |"aaaaaaaa\U{0019}aa\0a"| > 0 && forall i :: 0 <= i < |"aaaaaaaa\U{0019}aa\0a"| ==> IsDigit("aaaaaaaa\U{0019}aa\0a"[i]);
}

// REPEAT 5 - TIME: 85.6279796 s

method {:test} Test11() {
var r0 := IsInteger("9a9a7a4");
expect r0 <==> |"9a9a7a4"| > 0 && forall i :: 0 <= i < |"9a9a7a4"| ==> IsDigit("9a9a7a4"[i]);
}
method {:test} Test12() {
var r0 := IsInteger("aaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaa\t"[i]);
}

// REPEAT 6 - TIME: 105.5319915 s

method {:test} Test13() {
var r0 := IsInteger("aa1a0aaaaaaaaaa");
expect r0 <==> |"aa1a0aaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aa1a0aaaaaaaaaa"| ==> IsDigit("aa1a0aaaaaaaaaa"[i]);
}
method {:test} Test14() {
var r0 := IsInteger("aaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 7 - TIME: 128.8954258 s

method {:test} Test15() {
var r0 := IsInteger("aaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test16() {
var r0 := IsInteger("aaaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 8 - TIME: 162.780375 s

method {:test} Test17() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa"| ==> IsDigit("aaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test18() {
var r0 := IsInteger("aaaaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 9 - TIME: 191.6121132 s

method {:test} Test19() {
var r0 := IsInteger("aaaaaaa1aaaaaa01aa");
expect r0 <==> |"aaaaaaa1aaaaaa01aa"| > 0 && forall i :: 0 <= i < |"aaaaaaa1aaaaaa01aa"| ==> IsDigit("aaaaaaa1aaaaaa01aa"[i]);
}
method {:test} Test20() {
var r0 := IsInteger("aaaaaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 10 - TIME: 216.7199755 s

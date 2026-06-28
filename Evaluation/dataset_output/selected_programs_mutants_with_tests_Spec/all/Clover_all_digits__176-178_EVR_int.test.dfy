// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 0 to 0
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    if !(s[i] in "0123456789") {
      return false;
    }
  }
}


method {:test} Test0() {
var r0 := allDigits("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] in "0123456789";
}
method {:test} Test1() {
var r0 := allDigits("aaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 1 - TIME: 3.439608 s

method {:test} Test2() {
var r0 := allDigits("a9");
expect r0 <==> forall i :: 0 <= i < |"a9"| ==> "a9"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 4.7094652 s

method {:test} Test4() {
var r0 := allDigits("aaaaaa9");
expect r0 <==> forall i :: 0 <= i < |"aaaaaa9"| ==> "aaaaaa9"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}

// REPEAT 3 - TIME: 5.957381 s

method {:test} Test6() {
var r0 := allDigits("521aa0");
expect r0 <==> forall i :: 0 <= i < |"521aa0"| ==> "521aa0"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 7.4909804 s

method {:test} Test8() {
var r0 := allDigits("161a0");
expect r0 <==> forall i :: 0 <= i < |"161a0"| ==> "161a0"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\U{0002}aaaaaaa\U{0004}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaa\U{0004}\0"| ==> "\U{0002}aaaaaaa\U{0004}\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 9.3117709 s

method {:test} Test10() {
var r0 := allDigits("7a1aaaaaaaaaaaaaaaaaaaaaa0");
expect r0 <==> forall i :: 0 <= i < |"7a1aaaaaaaaaaaaaaaaaaaaaa0"| ==> "7a1aaaaaaaaaaaaaaaaaaaaaa0"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}"| ==> "\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}"[i] in "0123456789";
}

// REPEAT 6 - TIME: 10.7467515 s

method {:test} Test12() {
var r0 := allDigits("1a0");
expect r0 <==> forall i :: 0 <= i < |"1a0"| ==> "1a0"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("a\0aaa\U{0004}a\U{0006}a\U{0008}\n\U{000C}aa\U{0002}\U{0010}aaaaaa\U{000E}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaa\U{0004}a\U{0006}a\U{0008}\n\U{000C}aa\U{0002}\U{0010}aaaaaa\U{000E}"| ==> "a\0aaa\U{0004}a\U{0006}a\U{0008}\n\U{000C}aa\U{0002}\U{0010}aaaaaa\U{000E}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 11.9860942 s

method {:test} Test14() {
var r0 := allDigits("061a");
expect r0 <==> forall i :: 0 <= i < |"061a"| ==> "061a"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\U{0012}\U{0002}aaa\U{0006}aaa\U{0008}a\U{000C}aaa\U{0010}\U{0004}a\0a\na\U{000E}");
expect r0 <==> forall i :: 0 <= i < |"\U{0012}\U{0002}aaa\U{0006}aaa\U{0008}a\U{000C}aaa\U{0010}\U{0004}a\0a\na\U{000E}"| ==> "\U{0012}\U{0002}aaa\U{0006}aaa\U{0008}a\U{000C}aaa\U{0010}\U{0004}a\0a\na\U{000E}"[i] in "0123456789";
}

// REPEAT 8 - TIME: 13.241858 s

method {:test} Test16() {
var r0 := allDigits("23a0a");
expect r0 <==> forall i :: 0 <= i < |"23a0a"| ==> "23a0a"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\U{0008}\0a\U{0002}a\U{0006}\n\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\0a\U{0002}a\U{0006}\n\U{0004}"| ==> "\U{0008}\0a\U{0002}a\U{0006}\n\U{0004}"[i] in "0123456789";
}

// REPEAT 9 - TIME: 14.394231 s

method {:test} Test18() {
var r0 := allDigits("210");
expect r0 <==> forall i :: 0 <= i < |"210"| ==> "210"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\U{000E}\0\U{0010}aa\U{0004}\U{0002}\U{0008}a\U{000C}\U{0006}\n");
expect r0 <==> forall i :: 0 <= i < |"\U{000E}\0\U{0010}aa\U{0004}\U{0002}\U{0008}a\U{000C}\U{0006}\n"| ==> "\U{000E}\0\U{0010}aa\U{0004}\U{0002}\U{0008}a\U{000C}\U{0006}\n"[i] in "0123456789";
}

// REPEAT 10 - TIME: 15.8270274 s

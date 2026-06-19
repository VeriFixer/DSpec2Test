// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 1 to |s|
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

// REPEAT 1 - TIME: 2.8220137 s

method {:test} Test2() {
var r0 := allDigits("aaaaaa9");
expect r0 <==> forall i :: 0 <= i < |"aaaaaa9"| ==> "aaaaaa9"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("aaaaaaaa\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\U{0002}\0"| ==> "aaaaaaaa\U{0002}\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 4.2772897 s

method {:test} Test4() {
var r0 := allDigits("aaaaaaa9");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaa9"| ==> "aaaaaaa9"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("\0aaaaaaa\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaa\U{0004}\U{0002}"| ==> "\0aaaaaaa\U{0004}\U{0002}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 5.7785298 s

method {:test} Test6() {
var r0 := allDigits("3421a0");
expect r0 <==> forall i :: 0 <= i < |"3421a0"| ==> "3421a0"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\U{0002}aaaaa\U{0004}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaa\U{0004}\0"| ==> "\U{0002}aaaaa\U{0004}\0"[i] in "0123456789";
}

// REPEAT 4 - TIME: 7.8078852 s

method {:test} Test8() {
var r0 := allDigits("12a0aa");
expect r0 <==> forall i :: 0 <= i < |"12a0aa"| ==> "12a0aa"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\0aa\U{0002}aaa");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaa"| ==> "\0aa\U{0002}aaa"[i] in "0123456789";
}

// REPEAT 5 - TIME: 9.2477838 s

method {:test} Test10() {
var r0 := allDigits("23aaaaaa0aa");
expect r0 <==> forall i :: 0 <= i < |"23aaaaaa0aa"| ==> "23aaaaaa0aa"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}aaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaa\0a"| ==> "\U{0002}aaaaaaa\0a"[i] in "0123456789";
}

// REPEAT 6 - TIME: 10.5616597 s

method {:test} Test12() {
var r0 := allDigits("120aa");
expect r0 <==> forall i :: 0 <= i < |"120aa"| ==> "120aa"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("\U{0002}a\U{000E}aaa\0\U{0004}\U{0006}\U{0008}\n\U{000C}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}a\U{000E}aaa\0\U{0004}\U{0006}\U{0008}\n\U{000C}"| ==> "\U{0002}a\U{000E}aaa\0\U{0004}\U{0006}\U{0008}\n\U{000C}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 11.9465998 s

method {:test} Test14() {
var r0 := allDigits("2350a");
expect r0 <==> forall i :: 0 <= i < |"2350a"| ==> "2350a"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 13.2143557 s

method {:test} Test16() {
var r0 := allDigits("4501");
expect r0 <==> forall i :: 0 <= i < |"4501"| ==> "4501"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}

// REPEAT 9 - TIME: 14.7796671 s

method {:test} Test18() {
var r0 := allDigits("41aaaaa0a");
expect r0 <==> forall i :: 0 <= i < |"41aaaaa0a"| ==> "41aaaaa0a"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\U{0002}\U{0004}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\U{0004}\0"| ==> "\U{0002}\U{0004}\0"[i] in "0123456789";
}

// REPEAT 10 - TIME: 16.0188781 s

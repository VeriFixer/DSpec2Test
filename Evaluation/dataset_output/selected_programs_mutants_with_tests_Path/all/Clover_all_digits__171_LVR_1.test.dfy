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
var r0 := allDigits("a");
expect r0 <==> forall i :: 0 <= i < |"a"| ==> "a"[i] in "0123456789";
}
method {:test} Test1() {
var r0 := allDigits("aaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 1 - TIME: 16.3747568 s

method {:test} Test2() {
var r0 := allDigits("a9aaaaaaaaaaaaaa0");
expect r0 <==> forall i :: 0 <= i < |"a9aaaaaaaaaaaaaa0"| ==> "a9aaaaaaaaaaaaaa0"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("aaaaaaaaaaaaaaa\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaa\0\U{0002}"| ==> "aaaaaaaaaaaaaaa\0\U{0002}"[i] in "0123456789";
}

// REPEAT 2 - TIME: 27.6805252 s

method {:test} Test4() {
var r0 := allDigits("aa");
expect r0 <==> forall i :: 0 <= i < |"aa"| ==> "aa"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("aaaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\0a"| ==> "aaaaaaaa\0a"[i] in "0123456789";
}

// REPEAT 3 - TIME: 39.4415431 s

method {:test} Test6() {
var r0 := allDigits("99a");
expect r0 <==> forall i :: 0 <= i < |"99a"| ==> "99a"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("9\09");
expect r0 <==> forall i :: 0 <= i < |"9\09"| ==> "9\09"[i] in "0123456789";
}

// REPEAT 4 - TIME: 50.6601592 s

method {:test} Test8() {
var r0 := allDigits("10");
expect r0 <==> forall i :: 0 <= i < |"10"| ==> "10"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] in "0123456789";
}

// REPEAT 5 - TIME: 61.9065722 s

method {:test} Test10() {
var r0 := allDigits("120aa");
expect r0 <==> forall i :: 0 <= i < |"120aa"| ==> "120aa"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}\0aaaaaaa\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0aaaaaaa\U{0004}a"| ==> "\U{0002}\0aaaaaaa\U{0004}a"[i] in "0123456789";
}

// REPEAT 6 - TIME: 74.038194 s

method {:test} Test12() {
var r0 := allDigits("031aaaaa12");
expect r0 <==> forall i :: 0 <= i < |"031aaaaa12"| ==> "031aaaaa12"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("\U{0003}9a\U{0005}aaaaaaaaaaaa8\taaaaaaaaaa\U{0001}\U{0007}");
expect r0 <==> forall i :: 0 <= i < |"\U{0003}9a\U{0005}aaaaaaaaaaaa8\taaaaaaaaaa\U{0001}\U{0007}"| ==> "\U{0003}9a\U{0005}aaaaaaaaaaaa8\taaaaaaaaaa\U{0001}\U{0007}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 87.4454862 s

method {:test} Test14() {
var r0 := allDigits("2a9aaa0aa");
expect r0 <==> forall i :: 0 <= i < |"2a9aaa0aa"| ==> "2a9aaa0aa"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\0a99");
expect r0 <==> forall i :: 0 <= i < |"\0a99"| ==> "\0a99"[i] in "0123456789";
}

// REPEAT 8 - TIME: 100.5127749 s

method {:test} Test16() {
var r0 := allDigits("34a4aaa0aaaa");
expect r0 <==> forall i :: 0 <= i < |"34a4aaa0aaaa"| ==> "34a4aaa0aaaa"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\U{0002}aaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaa\0"| ==> "\U{0002}aaaaaaa\0"[i] in "0123456789";
}

// REPEAT 9 - TIME: 112.957276 s

method {:test} Test18() {
var r0 := allDigits("41aaaaa0aaaaaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"41aaaaa0aaaaaaaaaa"| ==> "41aaaaa0aaaaaaaaaa"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\U{0002}\U{0004}aaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\U{0004}aaaaaa\0"| ==> "\U{0002}\U{0004}aaaaaa\0"[i] in "0123456789";
}

// REPEAT 10 - TIME: 124.8816359 s

// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := !true;
  for i := 0 to |s|
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

// REPEAT 1 - TIME: 14.8034116 s

method {:test} Test2() {
var r0 := allDigits("10");
expect r0 <==> forall i :: 0 <= i < |"10"| ==> "10"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 25.4483525 s

method {:test} Test4() {
var r0 := allDigits("999");
expect r0 <==> forall i :: 0 <= i < |"999"| ==> "999"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("9a\U{0001}");
expect r0 <==> forall i :: 0 <= i < |"9a\U{0001}"| ==> "9a\U{0001}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 35.7853558 s

method {:test} Test6() {
var r0 := allDigits("9a99");
expect r0 <==> forall i :: 0 <= i < |"9a99"| ==> "9a99"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}

// REPEAT 4 - TIME: 46.4201181 s

method {:test} Test8() {
var r0 := allDigits("0a10");
expect r0 <==> forall i :: 0 <= i < |"0a10"| ==> "0a10"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("aaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaa\0"| ==> "aaaa\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 57.7014544 s

method {:test} Test10() {
var r0 := allDigits("989");
expect r0 <==> forall i :: 0 <= i < |"989"| ==> "989"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}a\0\U{0004}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}a\0\U{0004}\U{0006}"| ==> "\U{0002}a\0\U{0004}\U{0006}"[i] in "0123456789";
}

// REPEAT 6 - TIME: 68.2552992 s

method {:test} Test12() {
var r0 := allDigits("09");
expect r0 <==> forall i :: 0 <= i < |"09"| ==> "09"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("99a\0");
expect r0 <==> forall i :: 0 <= i < |"99a\0"| ==> "99a\0"[i] in "0123456789";
}

// REPEAT 7 - TIME: 78.7762549 s

method {:test} Test14() {
var r0 := allDigits("99a9a9a9aaaaaaaaa9aaaa9");
expect r0 <==> forall i :: 0 <= i < |"99a9a9a9aaaaaaaaa9aaaa9"| ==> "99a9a9a9aaaaaaaaa9aaaa9"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] in "0123456789";
}

// REPEAT 8 - TIME: 89.8174487 s

method {:test} Test16() {
var r0 := allDigits("01a");
expect r0 <==> forall i :: 0 <= i < |"01a"| ==> "01a"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\0aaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaa\U{0002}"| ==> "\0aaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 9 - TIME: 101.018608 s

method {:test} Test18() {
var r0 := allDigits("1999a");
expect r0 <==> forall i :: 0 <= i < |"1999a"| ==> "1999a"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 10 - TIME: 111.9837825 s

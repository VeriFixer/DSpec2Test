// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 0 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
  }
}


method {:test} Test0() {
var r0 := allDigits("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] in "0123456789";
}
method {:test} Test2() {
var r0 := allDigits("a");
expect r0 <==> forall i :: 0 <= i < |"a"| ==> "a"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("aa");
expect r0 <==> forall i :: 0 <= i < |"aa"| ==> "aa"[i] in "0123456789";
}
method {:test} Test8() {
var r0 := allDigits("aaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}
method {:test} Test10() {
var r0 := allDigits("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] in "0123456789";
}

// REPEAT 1 - TIME: 11.5059793 s

method {:test} Test15() {
var r0 := allDigits("3021");
expect r0 <==> forall i :: 0 <= i < |"3021"| ==> "3021"[i] in "0123456789";
}
method {:test} Test16() {
var r0 := allDigits("a\0aaaaaa\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaa\U{0004}\U{0002}"| ==> "a\0aaaaaa\U{0004}\U{0002}"[i] in "0123456789";
}

// REPEAT 2 - TIME: 13.347408 s

method {:test} Test17() {
var r0 := allDigits("9a9");
expect r0 <==> forall i :: 0 <= i < |"9a9"| ==> "9a9"[i] in "0123456789";
}
method {:test} Test18() {
var r0 := allDigits("\U{0002}\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}"| ==> "\U{0002}\0\U{0004}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 14.7634492 s

method {:test} Test19() {
var r0 := allDigits("3401aaaaaaaaaaaaaaaaaaaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"3401aaaaaaaaaaaaaaaaaaaaaaaa2"| ==> "3401aaaaaaaaaaaaaaaaaaaaaaaa2"[i] in "0123456789";
}
method {:test} Test20() {
var r0 := allDigits("\U{0002}\0a\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0a\U{0004}a"| ==> "\U{0002}\0a\U{0004}a"[i] in "0123456789";
}

// REPEAT 4 - TIME: 16.5190228 s

method {:test} Test21() {
var r0 := allDigits("99aaa9aaa9aaaaaaaaaaaaaaaa9aa9");
expect r0 <==> forall i :: 0 <= i < |"99aaa9aaa9aaaaaaaaaaaaaaaa9aa9"| ==> "99aaa9aaa9aaaaaaaaaaaaaaaa9aa9"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\0\U{0006}aa\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0006}aa\U{0002}\U{0004}"| ==> "\0\U{0006}aa\U{0002}\U{0004}"[i] in "0123456789";
}

// REPEAT 5 - TIME: 17.6428252 s

method {:test} Test23() {
var r0 := allDigits("150");
expect r0 <==> forall i :: 0 <= i < |"150"| ==> "150"[i] in "0123456789";
}
method {:test} Test24() {
var r0 := allDigits("\U{0008}\0a\U{0006}a\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\0a\U{0006}a\U{0002}\U{0004}"| ==> "\U{0008}\0a\U{0006}a\U{0002}\U{0004}"[i] in "0123456789";
}

// REPEAT 6 - TIME: 19.3861245 s

method {:test} Test25() {
var r0 := allDigits("2340a");
expect r0 <==> forall i :: 0 <= i < |"2340a"| ==> "2340a"[i] in "0123456789";
}
method {:test} Test26() {
var r0 := allDigits("\U{0004}\0\U{000C}aa\U{0008}a\U{0006}a\naa\U{0002}aaaaa");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{000C}aa\U{0008}a\U{0006}a\naa\U{0002}aaaaa"| ==> "\U{0004}\0\U{000C}aa\U{0008}a\U{0006}a\naa\U{0002}aaaaa"[i] in "0123456789";
}

// REPEAT 7 - TIME: 20.9888064 s

method {:test} Test27() {
var r0 := allDigits("0990");
expect r0 <==> forall i :: 0 <= i < |"0990"| ==> "0990"[i] in "0123456789";
}
method {:test} Test28() {
var r0 := allDigits("\U{0006}\U{0008}aa\U{0002}\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\U{0008}aa\U{0002}\0\U{0004}"| ==> "\U{0006}\U{0008}aa\U{0002}\0\U{0004}"[i] in "0123456789";
}

// REPEAT 8 - TIME: 22.5281274 s

method {:test} Test29() {
var r0 := allDigits("4620a1");
expect r0 <==> forall i :: 0 <= i < |"4620a1"| ==> "4620a1"[i] in "0123456789";
}
method {:test} Test30() {
var r0 := allDigits("\U{0002}\0a\U{0004}a\U{0008}\U{0006}\n");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0a\U{0004}a\U{0008}\U{0006}\n"| ==> "\U{0002}\0a\U{0004}a\U{0008}\U{0006}\n"[i] in "0123456789";
}

// REPEAT 9 - TIME: 24.3792956 s

method {:test} Test31() {
var r0 := allDigits("023");
expect r0 <==> forall i :: 0 <= i < |"023"| ==> "023"[i] in "0123456789";
}
method {:test} Test32() {
var r0 := allDigits("\U{0016}\0a\U{0006}a\U{0008}a\U{000E}\U{0018}\U{0014}aaaaaa\U{0012}a\U{0002}aa\U{000C}a\U{0004}aaa\na\U{0010}");
expect r0 <==> forall i :: 0 <= i < |"\U{0016}\0a\U{0006}a\U{0008}a\U{000E}\U{0018}\U{0014}aaaaaa\U{0012}a\U{0002}aa\U{000C}a\U{0004}aaa\na\U{0010}"| ==> "\U{0016}\0a\U{0006}a\U{0008}a\U{000E}\U{0018}\U{0014}aaaaaa\U{0012}a\U{0002}aa\U{000C}a\U{0004}aaa\na\U{0010}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 26.4231007 s

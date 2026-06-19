// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 0 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    return false;
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

// REPEAT 1 - TIME: 10.1744232 s

method {:test} Test15() {
var r0 := allDigits("0aaaaaaaaaaaa9aa");
expect r0 <==> forall i :: 0 <= i < |"0aaaaaaaaaaaa9aa"| ==> "0aaaaaaaaaaaa9aa"[i] in "0123456789";
}
method {:test} Test16() {
var r0 := allDigits("a\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"a\0\U{0002}"| ==> "a\0\U{0002}"[i] in "0123456789";
}

// REPEAT 2 - TIME: 11.2881327 s

method {:test} Test17() {
var r0 := allDigits("1090aaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"1090aaaaaaa"| ==> "1090aaaaaaa"[i] in "0123456789";
}
method {:test} Test18() {
var r0 := allDigits("\U{0004}\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{0002}"| ==> "\U{0004}\0\U{0002}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 12.4814386 s

method {:test} Test19() {
var r0 := allDigits("1210");
expect r0 <==> forall i :: 0 <= i < |"1210"| ==> "1210"[i] in "0123456789";
}
method {:test} Test20() {
var r0 := allDigits("\U{0004}\0\U{0006}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{0006}\U{0002}"| ==> "\U{0004}\0\U{0006}\U{0002}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 13.9714381 s

method {:test} Test21() {
var r0 := allDigits("210");
expect r0 <==> forall i :: 0 <= i < |"210"| ==> "210"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 15.6957661 s

method {:test} Test23() {
var r0 := allDigits("3aaaa0aaa1aaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"3aaaa0aaa1aaaaaaa"| ==> "3aaaa0aaa1aaaaaaa"[i] in "0123456789";
}
method {:test} Test24() {
var r0 := allDigits("\n\0aaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{0002}\U{0004}aa");
expect r0 <==> forall i :: 0 <= i < |"\n\0aaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{0002}\U{0004}aa"| ==> "\n\0aaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{0002}\U{0004}aa"[i] in "0123456789";
}

// REPEAT 6 - TIME: 16.898544 s

method {:test} Test25() {
var r0 := allDigits("2130a");
expect r0 <==> forall i :: 0 <= i < |"2130a"| ==> "2130a"[i] in "0123456789";
}
method {:test} Test26() {
var r0 := allDigits("\U{0006}\0\U{0002}\U{0008}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0\U{0002}\U{0008}\U{0004}"| ==> "\U{0006}\0\U{0002}\U{0008}\U{0004}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 18.1462504 s

method {:test} Test27() {
var r0 := allDigits("2021");
expect r0 <==> forall i :: 0 <= i < |"2021"| ==> "2021"[i] in "0123456789";
}
method {:test} Test28() {
var r0 := allDigits("\U{0002}\0a\U{0006}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0a\U{0006}\U{0004}"| ==> "\U{0002}\0a\U{0006}\U{0004}"[i] in "0123456789";
}

// REPEAT 8 - TIME: 19.5573426 s

method {:test} Test29() {
var r0 := allDigits("201");
expect r0 <==> forall i :: 0 <= i < |"201"| ==> "201"[i] in "0123456789";
}
method {:test} Test30() {
var r0 := allDigits("\U{000E}aaa\U{0010}\U{0006}aa\0\U{0008}\U{0004}\na\U{0002}aa\U{000C}");
expect r0 <==> forall i :: 0 <= i < |"\U{000E}aaa\U{0010}\U{0006}aa\0\U{0008}\U{0004}\na\U{0002}aa\U{000C}"| ==> "\U{000E}aaa\U{0010}\U{0006}aa\0\U{0008}\U{0004}\na\U{0002}aa\U{000C}"[i] in "0123456789";
}

// REPEAT 9 - TIME: 21.1590514 s

method {:test} Test31() {
var r0 := allDigits("410");
expect r0 <==> forall i :: 0 <= i < |"410"| ==> "410"[i] in "0123456789";
}
method {:test} Test32() {
var r0 := allDigits("\0\U{0018}aaa\naaa\U{000E}\U{0002}\U{0010}aa\U{0004}aaa\U{000C}\U{0006}aaaa\U{0008}\U{0012}aa\U{0014}\U{0016}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0018}aaa\naaa\U{000E}\U{0002}\U{0010}aa\U{0004}aaa\U{000C}\U{0006}aaaa\U{0008}\U{0012}aa\U{0014}\U{0016}"| ==> "\0\U{0018}aaa\naaa\U{000E}\U{0002}\U{0010}aa\U{0004}aaa\U{000C}\U{0006}aaaa\U{0008}\U{0012}aa\U{0014}\U{0016}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 22.7047005 s

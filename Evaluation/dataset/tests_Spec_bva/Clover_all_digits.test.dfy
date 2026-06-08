  method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
{
  result:=true ;
  for i := 0 to |s|
    invariant result <==> (forall ii :: 0 <= ii < i ==> s[ii] in "0123456789")
  {
    if ! (s[i] in "0123456789"){
      return false;
    }
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
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}
method {:test} Test10() {
var r0 := allDigits("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] in "0123456789";
}

// REPEAT 1 - TIME: 9.5942327 s

method {:test} Test15() {
var r0 := allDigits("09aa");
expect r0 <==> forall i :: 0 <= i < |"09aa"| ==> "09aa"[i] in "0123456789";
}
method {:test} Test16() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 10.6749603 s

method {:test} Test17() {
var r0 := allDigits("13aaaaaa0aaaaaaaaaaaaaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"13aaaaaa0aaaaaaaaaaaaaaaaaa2"| ==> "13aaaaaa0aaaaaaaaaaaaaaaaaa2"[i] in "0123456789";
}
method {:test} Test18() {
var r0 := allDigits("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 11.7317724 s

method {:test} Test19() {
var r0 := allDigits("235a4aaaaaaaaaaa1aaaaaaaa0");
expect r0 <==> forall i :: 0 <= i < |"235a4aaaaaaaaaaa1aaaaaaaa0"| ==> "235a4aaaaaaaaaaa1aaaaaaaa0"[i] in "0123456789";
}
method {:test} Test20() {
var r0 := allDigits("\U{0002}\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}"| ==> "\U{0002}\0\U{0004}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 13.7169816 s

method {:test} Test21() {
var r0 := allDigits("10");
expect r0 <==> forall i :: 0 <= i < |"10"| ==> "10"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\U{0002}\0\U{0004}\U{0008}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}\U{0008}\U{0006}"| ==> "\U{0002}\0\U{0004}\U{0008}\U{0006}"[i] in "0123456789";
}

// REPEAT 5 - TIME: 15.1118517 s

method {:test} Test23() {
var r0 := allDigits("310");
expect r0 <==> forall i :: 0 <= i < |"310"| ==> "310"[i] in "0123456789";
}
method {:test} Test24() {
var r0 := allDigits("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 6 - TIME: 16.5367221 s

method {:test} Test25() {
var r0 := allDigits("24a0aaaaaaaaaaaaaaaaaaaaaaa1");
expect r0 <==> forall i :: 0 <= i < |"24a0aaaaaaaaaaaaaaaaaaaaaaa1"| ==> "24a0aaaaaaaaaaaaaaaaaaaaaaa1"[i] in "0123456789";
}
method {:test} Test26() {
var r0 := allDigits("\U{0004}a\U{0002}aa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}a\U{0002}aa\0"| ==> "\U{0004}a\U{0002}aa\0"[i] in "0123456789";
}

// REPEAT 7 - TIME: 17.9829162 s

method {:test} Test27() {
var r0 := allDigits("30");
expect r0 <==> forall i :: 0 <= i < |"30"| ==> "30"[i] in "0123456789";
}
method {:test} Test28() {
var r0 := allDigits("\U{0002}aa\U{0006}a\U{0004}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aa\U{0006}a\U{0004}\0"| ==> "\U{0002}aa\U{0006}a\U{0004}\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 20.0411078 s

method {:test} Test29() {
var r0 := allDigits("410");
expect r0 <==> forall i :: 0 <= i < |"410"| ==> "410"[i] in "0123456789";
}
method {:test} Test30() {
var r0 := allDigits("\U{000C}\0aaa\U{0006}a\U{0008}aaa\U{000E}a\U{0004}aaaaaaa\U{0002}aaaa\n");
expect r0 <==> forall i :: 0 <= i < |"\U{000C}\0aaa\U{0006}a\U{0008}aaa\U{000E}a\U{0004}aaaaaaa\U{0002}aaaa\n"| ==> "\U{000C}\0aaa\U{0006}a\U{0008}aaa\U{000E}a\U{0004}aaaaaaa\U{0002}aaaa\n"[i] in "0123456789";
}

// REPEAT 9 - TIME: 21.3307645 s

method {:test} Test31() {
var r0 := allDigits("50");
expect r0 <==> forall i :: 0 <= i < |"50"| ==> "50"[i] in "0123456789";
}
method {:test} Test32() {
var r0 := allDigits("\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}"| ==> "\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 22.9157262 s

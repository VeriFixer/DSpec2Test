// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  for i := 0 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    if !(s[i] in "0123456789") {
      return false;
    }
  }
  result := true;
}


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
var r0 := allDigits("a");
expect r0 <==> forall i :: 0 <= i < |"a"| ==> "a"[i] in "0123456789";
}
method {:test} Test1() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 1 - TIME: 15.3710327 s

method {:test} Test2() {
var r0 := allDigits("a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0");
expect r0 <==> forall i :: 0 <= i < |"a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"| ==> "a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("a\0");
expect r0 <==> forall i :: 0 <= i < |"a\0"| ==> "a\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 25.6305274 s

method {:test} Test4() {
var r0 := allDigits("1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a");
expect r0 <==> forall i :: 0 <= i < |"1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a"| ==> "1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("aa\0");
expect r0 <==> forall i :: 0 <= i < |"aa\0"| ==> "aa\0"[i] in "0123456789";
}

// REPEAT 3 - TIME: 36.3716639 s

method {:test} Test6() {
var r0 := allDigits("99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9");
expect r0 <==> forall i :: 0 <= i < |"99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9"| ==> "99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\0aa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}"| ==> "\0aa\U{0002}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 47.0920284 s

method {:test} Test8() {
var r0 := allDigits("20");
expect r0 <==> forall i :: 0 <= i < |"20"| ==> "20"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\U{0002}0\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}0\0"| ==> "\U{0002}0\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 58.7103917 s

method {:test} Test10() {
var r0 := allDigits("132aaaaaaaaa0aaaaa");
expect r0 <==> forall i :: 0 <= i < |"132aaaaaaaaa0aaaaa"| ==> "132aaaaaaaaa0aaaaa"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a9a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a9a"| ==> "\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a9a"[i] in "0123456789";
}

// REPEAT 6 - TIME: 70.0581799 s

method {:test} Test12() {
var r0 := allDigits("18a0a");
expect r0 <==> forall i :: 0 <= i < |"18a0a"| ==> "18a0a"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("aaa\0a");
expect r0 <==> forall i :: 0 <= i < |"aaa\0a"| ==> "aaa\0a"[i] in "0123456789";
}

// REPEAT 7 - TIME: 81.6239468 s

method {:test} Test14() {
var r0 := allDigits("001aa");
expect r0 <==> forall i :: 0 <= i < |"001aa"| ==> "001aa"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 93.8573867 s

method {:test} Test16() {
var r0 := allDigits("99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999");
expect r0 <==> forall i :: 0 <= i < |"99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999"| ==> "99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a"| ==> "\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a"[i] in "0123456789";
}

// REPEAT 9 - TIME: 105.4303266 s

method {:test} Test18() {
var r0 := allDigits("99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999");
expect r0 <==> forall i :: 0 <= i < |"99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999"| ==> "99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\0aaaaa");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaa"| ==> "\0aaaaa"[i] in "0123456789";
}

// REPEAT 10 - TIME: 118.1566881 s

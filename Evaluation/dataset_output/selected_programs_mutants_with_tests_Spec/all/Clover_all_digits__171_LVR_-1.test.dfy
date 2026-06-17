// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := -1 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    if !(s[i] in "0123456789") {
      return false;
    }
  }
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
var r0 := allDigits("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] in "0123456789";
}
method {:test} Test1() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 1 - TIME: 3.6638156 s

method {:test} Test2() {
var r0 := allDigits("0");
expect r0 <==> forall i :: 0 <= i < |"0"| ==> "0"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 5.0065239 s

method {:test} Test4() {
var r0 := allDigits("09");
expect r0 <==> forall i :: 0 <= i < |"09"| ==> "09"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("a\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"a\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| ==> "a\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[i] in "0123456789";
}

// REPEAT 3 - TIME: 6.3647689 s

method {:test} Test6() {
var r0 := allDigits("3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2");
expect r0 <==> forall i :: 0 <= i < |"3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2"| ==> "3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"| ==> "a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"[i] in "0123456789";
}

// REPEAT 4 - TIME: 8.0238806 s

method {:test} Test8() {
var r0 := allDigits("4235aaaaa0aaaaaaaaaaaaaaaaa1");
expect r0 <==> forall i :: 0 <= i < |"4235aaaaa0aaaaaaaaaaaaaaaaa1"| ==> "4235aaaaa0aaaaaaaaaaaaaaaaa1"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\U{0006}\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0006}\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 5 - TIME: 10.1990652 s

method {:test} Test10() {
var r0 := allDigits("345aaaa1aaaaaaaaaaaa0aaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"345aaaa1aaaaaaaaaaaa0aaaaaaa2"| ==> "345aaaa1aaaaaaaaaaaa0aaaaaaa2"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 6 - TIME: 12.3183536 s

method {:test} Test12() {
var r0 := allDigits("3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa");
expect r0 <==> forall i :: 0 <= i < |"3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa"| ==> "3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 14.6524437 s

method {:test} Test14() {
var r0 := allDigits("12aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aa");
expect r0 <==> forall i :: 0 <= i < |"12aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aa"| ==> "12aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aa"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\U{0004}\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}\0"| ==> "\U{0004}\U{0002}\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 16.4116617 s

method {:test} Test16() {
var r0 := allDigits("0324aaaaaaaaaaaaaaaaaaaaaa1");
expect r0 <==> forall i :: 0 <= i < |"0324aaaaaaaaaaaaaaaaaaaaaa1"| ==> "0324aaaaaaaaaaaaaaaaaaaaaa1"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\U{0004}\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}\0"| ==> "\U{0004}\U{0002}\0"[i] in "0123456789";
}

// REPEAT 9 - TIME: 18.6571474 s

method {:test} Test18() {
var r0 := allDigits("20");
expect r0 <==> forall i :: 0 <= i < |"20"| ==> "20"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\U{0004}\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa\U{0006}\U{0008}\naaaaaaaa\U{000C}\U{000E}\U{0012}\U{0014}\U{0010}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa\U{0006}\U{0008}\naaaaaaaa\U{000C}\U{000E}\U{0012}\U{0014}\U{0010}"| ==> "\U{0004}\U{0002}aaaaaaaaaaaa\0aaaaaaaaaaaa\U{0006}\U{0008}\naaaaaaaa\U{000C}\U{000E}\U{0012}\U{0014}\U{0010}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 21.2373744 s

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

method {:test} Test0() {
var r0 := allDigits("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] in "0123456789";
}
method {:test} Test1() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}
method {:test} Test2() {
var r0 := allDigits("aaa9");
expect r0 <==> forall i: int {:trigger "aaa9"[i]} :: 0 <= i < |"aaa9"| ==> "aaa9"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("\0");
expect r0 <==> forall i: int {:trigger "\0"[i]} :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}
method {:test} Test4() {
var r0 := allDigits("90");
expect r0 <==> forall i: int {:trigger "90"[i]} :: 0 <= i < |"90"| ==> "90"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("\U{0002}\0");
expect r0 <==> forall i: int {:trigger "\U{0002}\0"[i]} :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] in "0123456789";
}
method {:test} Test6() {
var r0 := allDigits("13aaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa2aaa");
expect r0 <==> forall i: int {:trigger "13aaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa2aaa"[i]} :: 0 <= i < |"13aaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa2aaa"| ==> "13aaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa2aaa"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\U{0002}\0\U{0004}");
expect r0 <==> forall i: int {:trigger "\U{0002}\0\U{0004}"[i]} :: 0 <= i < |"\U{0002}\0\U{0004}"| ==> "\U{0002}\0\U{0004}"[i] in "0123456789";
}
method {:test} Test8() {
var r0 := allDigits("423aaaaa0aaaaaaaaaaaaaaaaaa1");
expect r0 <==> forall i: int {:trigger "423aaaaa0aaaaaaaaaaaaaaaaaa1"[i]} :: 0 <= i < |"423aaaaa0aaaaaaaaaaaaaaaaaa1"| ==> "423aaaaa0aaaaaaaaaaaaaaaaaa1"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\U{0004}\0\U{0002}a");
expect r0 <==> forall i: int {:trigger "\U{0004}\0\U{0002}a"[i]} :: 0 <= i < |"\U{0004}\0\U{0002}a"| ==> "\U{0004}\0\U{0002}a"[i] in "0123456789";
}
method {:test} Test10() {
var r0 := allDigits("2aaaa");
expect r0 <==> forall i: int {:trigger "2aaaa"[i]} :: 0 <= i < |"2aaaa"| ==> "2aaaa"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0006}\U{0004}\U{0002}a\0");
expect r0 <==> forall i: int {:trigger "\U{0006}\U{0004}\U{0002}a\0"[i]} :: 0 <= i < |"\U{0006}\U{0004}\U{0002}a\0"| ==> "\U{0006}\U{0004}\U{0002}a\0"[i] in "0123456789";
}

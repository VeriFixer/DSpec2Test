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
method {:test} Test15() {
var r0 := allDigits("4310aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2");
expect r0 <==> forall i: int {:trigger "4310aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2"[i]} :: 0 <= i < |"4310aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2"| ==> "4310aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2"[i] in "0123456789";
}
method {:test} Test16() {
var r0 := allDigits("\U{0002}\0\U{0004}");
expect r0 <==> forall i: int {:trigger "\U{0002}\0\U{0004}"[i]} :: 0 <= i < |"\U{0002}\0\U{0004}"| ==> "\U{0002}\0\U{0004}"[i] in "0123456789";
}

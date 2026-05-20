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
method {:test} Test17() {
var r0 := allDigits("0091");
expect r0 <==> forall i: int {:trigger "0091"[i]} :: 0 <= i < |"0091"| ==> "0091"[i] in "0123456789";
}
method {:test} Test18() {
var r0 := allDigits("\U{0002}\U{0006}\0aaaaaaaaaaa\U{0004}");
expect r0 <==> forall i: int {:trigger "\U{0002}\U{0006}\0aaaaaaaaaaa\U{0004}"[i]} :: 0 <= i < |"\U{0002}\U{0006}\0aaaaaaaaaaa\U{0004}"| ==> "\U{0002}\U{0006}\0aaaaaaaaaaa\U{0004}"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("128303");
expect r0 <==> forall i: int {:trigger "128303"[i]} :: 0 <= i < |"128303"| ==> "128303"[i] in "0123456789";
}
method {:test} Test20() {
var r0 := allDigits("\n\0a\U{0006}aaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0008}aaaaaaaaa\U{0004}a\U{000E}\U{000C}");
expect r0 <==> forall i: int {:trigger "\n\0a\U{0006}aaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0008}aaaaaaaaa\U{0004}a\U{000E}\U{000C}"[i]} :: 0 <= i < |"\n\0a\U{0006}aaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0008}aaaaaaaaa\U{0004}a\U{000E}\U{000C}"| ==> "\n\0a\U{0006}aaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0008}aaaaaaaaa\U{0004}a\U{000E}\U{000C}"[i] in "0123456789";
}

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
method {:test} Test21() {
var r0 := allDigits("21aaaaaaa0a2aa1aa");
expect r0 <==> forall i: int {:trigger "21aaaaaaa0a2aa1aa"[i]} :: 0 <= i < |"21aaaaaaa0a2aa1aa"| ==> "21aaaaaaa0a2aa1aa"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\0aaaaa\U{0008}aaaaa\U{0002}\U{0006}a\U{0004}");
expect r0 <==> forall i: int {:trigger "\0aaaaa\U{0008}aaaaa\U{0002}\U{0006}a\U{0004}"[i]} :: 0 <= i < |"\0aaaaa\U{0008}aaaaa\U{0002}\U{0006}a\U{0004}"| ==> "\0aaaaa\U{0008}aaaaa\U{0002}\U{0006}a\U{0004}"[i] in "0123456789";
}
method {:test} Test23() {
var r0 := allDigits("201aaaaaaaaaaaa");
expect r0 <==> forall i: int {:trigger "201aaaaaaaaaaaa"[i]} :: 0 <= i < |"201aaaaaaaaaaaa"| ==> "201aaaaaaaaaaaa"[i] in "0123456789";
}
method {:test} Test24() {
var r0 := allDigits("\U{0004}\U{0002}a\0a");
expect r0 <==> forall i: int {:trigger "\U{0004}\U{0002}a\0a"[i]} :: 0 <= i < |"\U{0004}\U{0002}a\0a"| ==> "\U{0004}\U{0002}a\0a"[i] in "0123456789";
}
method {:test} Test25() {
var r0 := allDigits("12310");
expect r0 <==> forall i: int {:trigger "12310"[i]} :: 0 <= i < |"12310"| ==> "12310"[i] in "0123456789";
}
method {:test} Test26() {
var r0 := allDigits("\U{0004}\0aa\U{0006}aaaaaaaaaa\n\U{000C}\U{000E}aaaaaaaaaaaaaaa\U{0002}aaaa\U{0014}\U{0010}aa\U{0008}a\U{0012}");
expect r0 <==> forall i: int {:trigger "\U{0004}\0aa\U{0006}aaaaaaaaaa\n\U{000C}\U{000E}aaaaaaaaaaaaaaa\U{0002}aaaa\U{0014}\U{0010}aa\U{0008}a\U{0012}"[i]} :: 0 <= i < |"\U{0004}\0aa\U{0006}aaaaaaaaaa\n\U{000C}\U{000E}aaaaaaaaaaaaaaa\U{0002}aaaa\U{0014}\U{0010}aa\U{0008}a\U{0012}"| ==> "\U{0004}\0aa\U{0006}aaaaaaaaaa\n\U{000C}\U{000E}aaaaaaaaaaaaaaa\U{0002}aaaa\U{0014}\U{0010}aa\U{0008}a\U{0012}"[i] in "0123456789";
}

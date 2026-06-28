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

method {:test} Test14() {
var r0 := allDigits("061a");
expect r0 <==> forall i :: 0 <= i < |"061a"| ==> "061a"[i] in "0123456789";
}
method {:test} Test15() {
var r0 := allDigits("\U{0012}\U{0002}aaa\U{0006}aaa\U{0008}a\U{000C}aaa\U{0010}\U{0004}a\0a\na\U{000E}");
expect r0 <==> forall i :: 0 <= i < |"\U{0012}\U{0002}aaa\U{0006}aaa\U{0008}a\U{000C}aaa\U{0010}\U{0004}a\0a\na\U{000E}"| ==> "\U{0012}\U{0002}aaa\U{0006}aaa\U{0008}a\U{000C}aaa\U{0010}\U{0004}a\0a\na\U{000E}"[i] in "0123456789";
}

// REPEAT 8 - TIME: 13.241858 s

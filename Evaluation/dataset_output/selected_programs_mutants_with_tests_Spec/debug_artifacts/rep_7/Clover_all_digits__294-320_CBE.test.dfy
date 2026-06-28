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

method {:test} Test12() {
var r0 := allDigits("1a0");
expect r0 <==> forall i :: 0 <= i < |"1a0"| ==> "1a0"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("a\0aaa\U{0004}a\U{0006}a\U{0008}\n\U{000C}aa\U{0002}\U{0010}aaaaaa\U{000E}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaa\U{0004}a\U{0006}a\U{0008}\n\U{000C}aa\U{0002}\U{0010}aaaaaa\U{000E}"| ==> "a\0aaa\U{0004}a\U{0006}a\U{0008}\n\U{000C}aa\U{0002}\U{0010}aaaaaa\U{000E}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 11.9860942 s

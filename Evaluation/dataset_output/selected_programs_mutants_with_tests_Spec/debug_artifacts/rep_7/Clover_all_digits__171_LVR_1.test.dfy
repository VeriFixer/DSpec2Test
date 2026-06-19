// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 1 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    if !(s[i] in "0123456789") {
      return false;
    }
  }
}

method {:test} Test12() {
var r0 := allDigits("120aa");
expect r0 <==> forall i :: 0 <= i < |"120aa"| ==> "120aa"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("\U{0002}a\U{000E}aaa\0\U{0004}\U{0006}\U{0008}\n\U{000C}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}a\U{000E}aaa\0\U{0004}\U{0006}\U{0008}\n\U{000C}"| ==> "\U{0002}a\U{000E}aaa\0\U{0004}\U{0006}\U{0008}\n\U{000C}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 11.9465998 s

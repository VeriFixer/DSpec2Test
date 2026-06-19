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

method {:test} Test29() {
var r0 := allDigits("201");
expect r0 <==> forall i :: 0 <= i < |"201"| ==> "201"[i] in "0123456789";
}
method {:test} Test30() {
var r0 := allDigits("\U{000E}aaa\U{0010}\U{0006}aa\0\U{0008}\U{0004}\na\U{0002}aa\U{000C}");
expect r0 <==> forall i :: 0 <= i < |"\U{000E}aaa\U{0010}\U{0006}aa\0\U{0008}\U{0004}\na\U{0002}aa\U{000C}"| ==> "\U{000E}aaa\U{0010}\U{0006}aa\0\U{0008}\U{0004}\na\U{0002}aa\U{000C}"[i] in "0123456789";
}

// REPEAT 9 - TIME: 21.1590514 s

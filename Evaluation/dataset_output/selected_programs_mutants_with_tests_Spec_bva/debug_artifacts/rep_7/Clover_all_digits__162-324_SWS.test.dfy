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

method {:test} Test25() {
var r0 := allDigits("2340a");
expect r0 <==> forall i :: 0 <= i < |"2340a"| ==> "2340a"[i] in "0123456789";
}
method {:test} Test26() {
var r0 := allDigits("\U{0004}\0\U{000C}aa\U{0008}a\U{0006}a\naa\U{0002}aaaaa");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{000C}aa\U{0008}a\U{0006}a\naa\U{0002}aaaaa"| ==> "\U{0004}\0\U{000C}aa\U{0008}a\U{0006}a\naa\U{0002}aaaaa"[i] in "0123456789";
}

// REPEAT 7 - TIME: 20.9888064 s

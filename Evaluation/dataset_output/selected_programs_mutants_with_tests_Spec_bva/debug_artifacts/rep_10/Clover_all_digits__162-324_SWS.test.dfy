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

method {:test} Test31() {
var r0 := allDigits("023");
expect r0 <==> forall i :: 0 <= i < |"023"| ==> "023"[i] in "0123456789";
}
method {:test} Test32() {
var r0 := allDigits("\U{0016}\0a\U{0006}a\U{0008}a\U{000E}\U{0018}\U{0014}aaaaaa\U{0012}a\U{0002}aa\U{000C}a\U{0004}aaa\na\U{0010}");
expect r0 <==> forall i :: 0 <= i < |"\U{0016}\0a\U{0006}a\U{0008}a\U{000E}\U{0018}\U{0014}aaaaaa\U{0012}a\U{0002}aa\U{000C}a\U{0004}aaa\na\U{0010}"| ==> "\U{0016}\0a\U{0006}a\U{0008}a\U{000E}\U{0018}\U{0014}aaaaaa\U{0012}a\U{0002}aa\U{000C}a\U{0004}aaa\na\U{0010}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 26.4231007 s

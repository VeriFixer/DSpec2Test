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

method {:test} Test12() {
var r0 := allDigits("3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa");
expect r0 <==> forall i :: 0 <= i < |"3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa"| ==> "3452aaaaaaaaaaaaaaaaaaaaa0aaaaaaa1aaaa"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0008}a\U{0004}\U{0006}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 14.6524437 s

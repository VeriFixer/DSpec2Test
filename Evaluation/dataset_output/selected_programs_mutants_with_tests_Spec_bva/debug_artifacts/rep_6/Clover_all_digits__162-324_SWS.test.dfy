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

method {:test} Test23() {
var r0 := allDigits("3aaaa0aaa1aaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"3aaaa0aaa1aaaaaaa"| ==> "3aaaa0aaa1aaaaaaa"[i] in "0123456789";
}
method {:test} Test24() {
var r0 := allDigits("\n\0aaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{0002}\U{0004}aa");
expect r0 <==> forall i :: 0 <= i < |"\n\0aaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{0002}\U{0004}aa"| ==> "\n\0aaaaaaa\U{0008}aaaaaa\U{0006}aaaaaaaa\U{0002}\U{0004}aa"[i] in "0123456789";
}

// REPEAT 6 - TIME: 17.1909917 s

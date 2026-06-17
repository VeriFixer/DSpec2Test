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

method {:test} Test16() {
var r0 := allDigits("99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999");
expect r0 <==> forall i :: 0 <= i < |"99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999"| ==> "99a9aaaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaa9a99999"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a"| ==> "\0aa\U{0002}aaaaaaaaaaaaaa\U{000C}\U{0004}aaaa\U{0008}aa\U{0006}aaaaaaaaaaa\U{000E}\U{0010}\n\U{0012}a"[i] in "0123456789";
}

// REPEAT 9 - TIME: 105.4303266 s

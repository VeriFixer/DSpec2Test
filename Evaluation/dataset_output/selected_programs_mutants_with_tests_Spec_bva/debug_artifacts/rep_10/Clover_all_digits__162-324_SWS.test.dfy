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
var r0 := allDigits("410");
expect r0 <==> forall i :: 0 <= i < |"410"| ==> "410"[i] in "0123456789";
}
method {:test} Test32() {
var r0 := allDigits("\0\U{0018}aaa\naaa\U{000E}\U{0002}\U{0010}aa\U{0004}aaa\U{000C}\U{0006}aaaa\U{0008}\U{0012}aa\U{0014}\U{0016}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0018}aaa\naaa\U{000E}\U{0002}\U{0010}aa\U{0004}aaa\U{000C}\U{0006}aaaa\U{0008}\U{0012}aa\U{0014}\U{0016}"| ==> "\0\U{0018}aaa\naaa\U{000E}\U{0002}\U{0010}aa\U{0004}aaa\U{000C}\U{0006}aaaa\U{0008}\U{0012}aa\U{0014}\U{0016}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 22.2313358 s

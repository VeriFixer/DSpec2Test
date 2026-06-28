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

method {:test} Test9() {
var r0 := allDigits("\0aa\U{0002}\U{0004}aaaaa\U{0006}\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}\U{0004}aaaaa\U{0006}\U{0008}"| ==> "\0aa\U{0002}\U{0004}aaaaa\U{0006}\U{0008}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 8.217015 s

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
var r0 := allDigits("50");
expect r0 <==> forall i :: 0 <= i < |"50"| ==> "50"[i] in "0123456789";
}
method {:test} Test32() {
var r0 := allDigits("\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}"| ==> "\n\U{0008}a\U{0004}a\0\U{0006}\U{0002}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 21.1861843 s

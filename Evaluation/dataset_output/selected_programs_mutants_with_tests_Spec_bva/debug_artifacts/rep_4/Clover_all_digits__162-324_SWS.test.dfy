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

method {:test} Test19() {
var r0 := allDigits("3401aaaaaaaaaaaaaaaaaaaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"3401aaaaaaaaaaaaaaaaaaaaaaaa2"| ==> "3401aaaaaaaaaaaaaaaaaaaaaaaa2"[i] in "0123456789";
}
method {:test} Test20() {
var r0 := allDigits("\U{0002}\0a\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0a\U{0004}a"| ==> "\U{0002}\0a\U{0004}a"[i] in "0123456789";
}

// REPEAT 4 - TIME: 16.5190228 s

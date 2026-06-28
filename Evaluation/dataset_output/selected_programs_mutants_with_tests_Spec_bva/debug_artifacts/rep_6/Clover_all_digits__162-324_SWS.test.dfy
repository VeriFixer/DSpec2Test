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
var r0 := allDigits("150");
expect r0 <==> forall i :: 0 <= i < |"150"| ==> "150"[i] in "0123456789";
}
method {:test} Test24() {
var r0 := allDigits("\U{0008}\0a\U{0006}a\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\0a\U{0006}a\U{0002}\U{0004}"| ==> "\U{0008}\0a\U{0006}a\U{0002}\U{0004}"[i] in "0123456789";
}

// REPEAT 6 - TIME: 19.3861245 s

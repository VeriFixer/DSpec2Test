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

method {:test} Test27() {
var r0 := allDigits("30");
expect r0 <==> forall i :: 0 <= i < |"30"| ==> "30"[i] in "0123456789";
}
method {:test} Test28() {
var r0 := allDigits("\U{0002}aa\U{0006}a\U{0004}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aa\U{0006}a\U{0004}\0"| ==> "\U{0002}aa\U{0006}a\U{0004}\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 18.5185808 s

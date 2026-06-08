// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 0 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    return false;
  }
}

method {:test} Test8() {
var r0 := allDigits("20");
expect r0 <==> forall i :: 0 <= i < |"20"| ==> "20"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\U{0002}0\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}0\0"| ==> "\U{0002}0\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 44.6695759 s

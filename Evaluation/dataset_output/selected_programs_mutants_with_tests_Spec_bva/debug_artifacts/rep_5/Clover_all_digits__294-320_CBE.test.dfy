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

method {:test} Test21() {
var r0 := allDigits("10");
expect r0 <==> forall i :: 0 <= i < |"10"| ==> "10"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\U{0002}\0\U{0004}\U{0008}\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}\U{0008}\U{0006}"| ==> "\U{0002}\0\U{0004}\U{0008}\U{0006}"[i] in "0123456789";
}

// REPEAT 5 - TIME: 15.9062413 s

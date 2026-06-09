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
var r0 := allDigits("235a4aaaaaaaaaaa1aaaaaaaa0");
expect r0 <==> forall i :: 0 <= i < |"235a4aaaaaaaaaaa1aaaaaaaa0"| ==> "235a4aaaaaaaaaaa1aaaaaaaa0"[i] in "0123456789";
}
method {:test} Test20() {
var r0 := allDigits("\U{0002}\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}"| ==> "\U{0002}\0\U{0004}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 12.4637725 s

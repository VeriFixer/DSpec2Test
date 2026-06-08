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

method {:test} Test8() {
var r0 := allDigits("4235aaaaa0aaaaaaaaaaaaaaaaa1");
expect r0 <==> forall i :: 0 <= i < |"4235aaaaa0aaaaaaaaaaaaaaaaa1"| ==> "4235aaaaa0aaaaaaaaaaaaaaaaa1"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\U{0006}\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0006}\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 5 - TIME: 10.2331 s

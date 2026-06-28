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

method {:test} Test29() {
var r0 := allDigits("4620a1");
expect r0 <==> forall i :: 0 <= i < |"4620a1"| ==> "4620a1"[i] in "0123456789";
}
method {:test} Test30() {
var r0 := allDigits("\U{0002}\0a\U{0004}a\U{0008}\U{0006}\n");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0a\U{0004}a\U{0008}\U{0006}\n"| ==> "\U{0002}\0a\U{0004}a\U{0008}\U{0006}\n"[i] in "0123456789";
}

// REPEAT 9 - TIME: 24.3792956 s

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

method {:test} Test18() {
var r0 := allDigits("210");
expect r0 <==> forall i :: 0 <= i < |"210"| ==> "210"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\U{000E}\0\U{0010}aa\U{0004}\U{0002}\U{0008}a\U{000C}\U{0006}\n");
expect r0 <==> forall i :: 0 <= i < |"\U{000E}\0\U{0010}aa\U{0004}\U{0002}\U{0008}a\U{000C}\U{0006}\n"| ==> "\U{000E}\0\U{0010}aa\U{0004}\U{0002}\U{0008}a\U{000C}\U{0006}\n"[i] in "0123456789";
}

// REPEAT 10 - TIME: 15.8270274 s

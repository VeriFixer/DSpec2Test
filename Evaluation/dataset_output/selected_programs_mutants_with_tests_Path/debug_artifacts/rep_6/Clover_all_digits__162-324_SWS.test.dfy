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

method {:test} Test10() {
var r0 := allDigits("120aa");
expect r0 <==> forall i :: 0 <= i < |"120aa"| ==> "120aa"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}\0aaaaaaa\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0aaaaaaa\U{0004}a"| ==> "\U{0002}\0aaaaaaa\U{0004}a"[i] in "0123456789";
}

// REPEAT 6 - TIME: 74.038194 s

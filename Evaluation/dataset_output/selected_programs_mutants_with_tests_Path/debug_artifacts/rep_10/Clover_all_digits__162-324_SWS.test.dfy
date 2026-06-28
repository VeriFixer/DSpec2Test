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
var r0 := allDigits("41aaaaa0aaaaaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"41aaaaa0aaaaaaaaaa"| ==> "41aaaaa0aaaaaaaaaa"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\U{0002}\U{0004}aaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\U{0004}aaaaaa\0"| ==> "\U{0002}\U{0004}aaaaaa\0"[i] in "0123456789";
}

// REPEAT 10 - TIME: 124.8816359 s

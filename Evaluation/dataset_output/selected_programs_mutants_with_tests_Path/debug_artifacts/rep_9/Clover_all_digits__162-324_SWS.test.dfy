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

method {:test} Test16() {
var r0 := allDigits("01a");
expect r0 <==> forall i :: 0 <= i < |"01a"| ==> "01a"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\0aaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaa\U{0002}"| ==> "\0aaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 9 - TIME: 101.018608 s

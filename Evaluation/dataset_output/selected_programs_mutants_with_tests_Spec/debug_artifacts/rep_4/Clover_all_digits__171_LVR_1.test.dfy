// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 1 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    if !(s[i] in "0123456789") {
      return false;
    }
  }
}

method {:test} Test6() {
var r0 := allDigits("3421a0");
expect r0 <==> forall i :: 0 <= i < |"3421a0"| ==> "3421a0"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\U{0002}aaaaa\U{0004}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaa\U{0004}\0"| ==> "\U{0002}aaaaa\U{0004}\0"[i] in "0123456789";
}

// REPEAT 4 - TIME: 7.6387444 s

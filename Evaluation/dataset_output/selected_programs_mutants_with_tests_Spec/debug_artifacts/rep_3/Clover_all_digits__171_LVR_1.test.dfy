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

method {:test} Test4() {
var r0 := allDigits("aaaaaaa9");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaa9"| ==> "aaaaaaa9"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("\0aaaaaaa\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaa\U{0004}\U{0002}"| ==> "\0aaaaaaa\U{0004}\U{0002}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 6.054036 s

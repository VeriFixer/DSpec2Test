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

method {:test} Test15() {
var r0 := allDigits("3021");
expect r0 <==> forall i :: 0 <= i < |"3021"| ==> "3021"[i] in "0123456789";
}
method {:test} Test16() {
var r0 := allDigits("a\0aaaaaa\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaa\U{0004}\U{0002}"| ==> "a\0aaaaaa\U{0004}\U{0002}"[i] in "0123456789";
}

// REPEAT 2 - TIME: 13.347408 s

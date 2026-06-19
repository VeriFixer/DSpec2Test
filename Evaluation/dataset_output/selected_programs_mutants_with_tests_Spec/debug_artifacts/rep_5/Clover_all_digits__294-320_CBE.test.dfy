// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 0 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    return false;
  }
}

method {:test} Test8() {
var r0 := allDigits("12a0aa");
expect r0 <==> forall i :: 0 <= i < |"12a0aa"| ==> "12a0aa"[i] in "0123456789";
}
method {:test} Test9() {
var r0 := allDigits("\0aa\U{0002}aaa");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaa"| ==> "\0aa\U{0002}aaa"[i] in "0123456789";
}

// REPEAT 5 - TIME: 9.2477838 s

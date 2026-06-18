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

method {:test} Test15() {
var r0 := allDigits("0aaaaaaaaaaaa9aa");
expect r0 <==> forall i :: 0 <= i < |"0aaaaaaaaaaaa9aa"| ==> "0aaaaaaaaaaaa9aa"[i] in "0123456789";
}
method {:test} Test16() {
var r0 := allDigits("a\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"a\0\U{0002}"| ==> "a\0\U{0002}"[i] in "0123456789";
}

// REPEAT 2 - TIME: 11.1770873 s

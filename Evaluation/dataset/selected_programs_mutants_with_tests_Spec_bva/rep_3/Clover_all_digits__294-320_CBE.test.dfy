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

method {:test} Test17() {
var r0 := allDigits("13aaaaaa0aaaaaaaaaaaaaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"13aaaaaa0aaaaaaaaaaaaaaaaaa2"| ==> "13aaaaaa0aaaaaaaaaaaaaaaaaa2"[i] in "0123456789";
}
method {:test} Test18() {
var r0 := allDigits("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| ==> "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"[i] in "0123456789";
}

// REPEAT 3 - TIME: 11.0670234 s

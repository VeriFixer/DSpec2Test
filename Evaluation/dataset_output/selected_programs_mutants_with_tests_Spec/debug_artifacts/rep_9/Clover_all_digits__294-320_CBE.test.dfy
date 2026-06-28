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

method {:test} Test16() {
var r0 := allDigits("23a0a");
expect r0 <==> forall i :: 0 <= i < |"23a0a"| ==> "23a0a"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\U{0008}\0a\U{0002}a\U{0006}\n\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\0a\U{0002}a\U{0006}\n\U{0004}"| ==> "\U{0008}\0a\U{0002}a\U{0006}\n\U{0004}"[i] in "0123456789";
}

// REPEAT 9 - TIME: 14.394231 s

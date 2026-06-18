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

method {:test} Test6() {
var r0 := allDigits("\0aaaaa\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaa\U{0002}\U{0004}"| ==> "\0aaaaa\U{0002}\U{0004}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 6.4535415 s

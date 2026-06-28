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

method {:test} Test5() {
var r0 := allDigits("9a\0aaaaaaaaaaaaaaaaa99");
expect r0 <==> forall i :: 0 <= i < |"9a\0aaaaaaaaaaaaaaaaa99"| ==> "9a\0aaaaaaaaaaaaaaaaa99"[i] in "0123456789";
}

// REPEAT 6 - TIME: 5.870871 s

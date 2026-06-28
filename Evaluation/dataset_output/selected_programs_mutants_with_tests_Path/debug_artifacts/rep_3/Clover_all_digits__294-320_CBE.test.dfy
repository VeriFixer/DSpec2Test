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

method {:test} Test4() {
var r0 := allDigits("aa");
expect r0 <==> forall i :: 0 <= i < |"aa"| ==> "aa"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("aaaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\0a"| ==> "aaaaaaaa\0a"[i] in "0123456789";
}

// REPEAT 3 - TIME: 39.4415431 s

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

method {:test} Test16() {
var r0 := allDigits("34a4aaa0aaaa");
expect r0 <==> forall i :: 0 <= i < |"34a4aaa0aaaa"| ==> "34a4aaa0aaaa"[i] in "0123456789";
}
method {:test} Test17() {
var r0 := allDigits("\U{0002}aaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaa\0"| ==> "\U{0002}aaaaaaa\0"[i] in "0123456789";
}

// REPEAT 9 - TIME: 112.957276 s

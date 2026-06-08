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

method {:test} Test6() {
var r0 := allDigits("99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9");
expect r0 <==> forall i :: 0 <= i < |"99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9"| ==> "99aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a9"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\0aa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}"| ==> "\0aa\U{0002}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 35.1137047 s

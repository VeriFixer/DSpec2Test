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

method {:test} Test21() {
var r0 := allDigits("99aaa9aaa9aaaaaaaaaaaaaaaa9aa9");
expect r0 <==> forall i :: 0 <= i < |"99aaa9aaa9aaaaaaaaaaaaaaaa9aa9"| ==> "99aaa9aaa9aaaaaaaaaaaaaaaa9aa9"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\0\U{0006}aa\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0006}aa\U{0002}\U{0004}"| ==> "\0\U{0006}aa\U{0002}\U{0004}"[i] in "0123456789";
}

// REPEAT 5 - TIME: 17.6428252 s

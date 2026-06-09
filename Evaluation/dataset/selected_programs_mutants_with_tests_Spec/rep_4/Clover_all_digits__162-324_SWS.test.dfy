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
var r0 := allDigits("3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2");
expect r0 <==> forall i :: 0 <= i < |"3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2"| ==> "3aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1aa0a2"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"| ==> "a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}a"[i] in "0123456789";
}

// REPEAT 4 - TIME: 7.0832023 s

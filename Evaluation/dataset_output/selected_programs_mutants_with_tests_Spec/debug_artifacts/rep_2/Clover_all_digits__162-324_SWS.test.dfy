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

method {:test} Test2() {
var r0 := allDigits("aaaaaa9");
expect r0 <==> forall i :: 0 <= i < |"aaaaaa9"| ==> "aaaaaa9"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("aaaaaaaa\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\U{0002}\0"| ==> "aaaaaaaa\U{0002}\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 4.2772897 s

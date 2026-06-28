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
var r0 := allDigits("a\0aaaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaa"| ==> "a\0aaaaaaaa"[i] in "0123456789";
}

// REPEAT 7 - TIME: 6.5071174 s

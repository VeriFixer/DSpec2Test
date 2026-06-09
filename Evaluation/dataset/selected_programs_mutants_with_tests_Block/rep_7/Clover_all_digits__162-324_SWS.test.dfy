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
var r0 := allDigits("\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t");
expect r0 <==> forall i :: 0 <= i < |"\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t"| ==> "\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t"[i] in "0123456789";
}

// REPEAT 7 - TIME: 6.4295425 s

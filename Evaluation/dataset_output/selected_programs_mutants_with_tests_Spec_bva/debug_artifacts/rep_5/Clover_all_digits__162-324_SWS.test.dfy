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
var r0 := allDigits("210");
expect r0 <==> forall i :: 0 <= i < |"210"| ==> "210"[i] in "0123456789";
}
method {:test} Test22() {
var r0 := allDigits("\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 15.9430472 s

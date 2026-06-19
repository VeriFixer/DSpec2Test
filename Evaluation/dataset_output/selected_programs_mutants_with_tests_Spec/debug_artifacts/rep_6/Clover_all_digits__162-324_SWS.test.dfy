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

method {:test} Test10() {
var r0 := allDigits("23aaaaaa0aa");
expect r0 <==> forall i :: 0 <= i < |"23aaaaaa0aa"| ==> "23aaaaaa0aa"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0002}aaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaa\0a"| ==> "\U{0002}aaaaaaa\0a"[i] in "0123456789";
}

// REPEAT 6 - TIME: 10.5616597 s

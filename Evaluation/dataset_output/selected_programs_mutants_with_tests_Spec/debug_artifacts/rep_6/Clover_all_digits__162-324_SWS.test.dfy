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
var r0 := allDigits("345aaaa1aaaaaaaaaaaa0aaaaaaa2");
expect r0 <==> forall i :: 0 <= i < |"345aaaa1aaaaaaaaaaaa0aaaaaaa2"| ==> "345aaaa1aaaaaaaaaaaa0aaaaaaa2"[i] in "0123456789";
}
method {:test} Test11() {
var r0 := allDigits("\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}"| ==> "\U{0006}\0aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}"[i] in "0123456789";
}

// REPEAT 6 - TIME: 12.3183536 s

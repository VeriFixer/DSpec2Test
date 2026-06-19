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

method {:test} Test25() {
var r0 := allDigits("2130a");
expect r0 <==> forall i :: 0 <= i < |"2130a"| ==> "2130a"[i] in "0123456789";
}
method {:test} Test26() {
var r0 := allDigits("\U{0006}\0\U{0002}\U{0008}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0\U{0002}\U{0008}\U{0004}"| ==> "\U{0006}\0\U{0002}\U{0008}\U{0004}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 18.1462504 s

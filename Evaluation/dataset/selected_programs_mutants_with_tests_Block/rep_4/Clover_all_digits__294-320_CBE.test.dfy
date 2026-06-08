// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 0 to |s|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    return false;
  }
}

method {:test} Test3() {
var r0 := allDigits("0\U{0001}");
expect r0 <==> forall i :: 0 <= i < |"0\U{0001}"| ==> "0\U{0001}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 3.920021 s

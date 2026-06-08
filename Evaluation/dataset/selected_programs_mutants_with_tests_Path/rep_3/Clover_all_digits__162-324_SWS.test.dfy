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

method {:test} Test4() {
var r0 := allDigits("1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a");
expect r0 <==> forall i :: 0 <= i < |"1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a"| ==> "1a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("aa\0");
expect r0 <==> forall i :: 0 <= i < |"aa\0"| ==> "aa\0"[i] in "0123456789";
}

// REPEAT 3 - TIME: 26.9360251 s

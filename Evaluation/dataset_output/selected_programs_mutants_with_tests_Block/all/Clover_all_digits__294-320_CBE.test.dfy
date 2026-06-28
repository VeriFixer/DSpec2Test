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


method {:test} Test0() {
var r0 := allDigits("aaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 1 - TIME: 2.1550916 s

method {:test} Test1() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 2.8516117 s

method {:test} Test2() {
var r0 := allDigits("a\0");
expect r0 <==> forall i :: 0 <= i < |"a\0"| ==> "a\0"[i] in "0123456789";
}

// REPEAT 3 - TIME: 3.6600974 s

method {:test} Test3() {
var r0 := allDigits("9\U{0001}");
expect r0 <==> forall i :: 0 <= i < |"9\U{0001}"| ==> "9\U{0001}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 4.4816659 s

method {:test} Test4() {
var r0 := allDigits("\U{0002}a\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}a\0"| ==> "\U{0002}a\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 5.1271402 s

method {:test} Test5() {
var r0 := allDigits("9a\0aaaaaaaaaaaaaaaaa99");
expect r0 <==> forall i :: 0 <= i < |"9a\0aaaaaaaaaaaaaaaaa99"| ==> "9a\0aaaaaaaaaaaaaaaaa99"[i] in "0123456789";
}

// REPEAT 6 - TIME: 5.870871 s

method {:test} Test6() {
var r0 := allDigits("a\0aaaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaa"| ==> "a\0aaaaaaaa"[i] in "0123456789";
}

// REPEAT 7 - TIME: 6.5071174 s

method {:test} Test7() {
var r0 := allDigits("\U{0003}0a\U{0001}");
expect r0 <==> forall i :: 0 <= i < |"\U{0003}0a\U{0001}"| ==> "\U{0003}0a\U{0001}"[i] in "0123456789";
}

// REPEAT 8 - TIME: 7.111407 s

method {:test} Test8() {
var r0 := allDigits("aaaaa\0aaaaa");
expect r0 <==> forall i :: 0 <= i < |"aaaaa\0aaaaa"| ==> "aaaaa\0aaaaa"[i] in "0123456789";
}

// REPEAT 9 - TIME: 7.6154679 s

method {:test} Test9() {
var r0 := allDigits("\0aa\U{0002}\U{0004}aaaaa\U{0006}\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}\U{0004}aaaaa\U{0006}\U{0008}"| ==> "\0aa\U{0002}\U{0004}aaaaa\U{0006}\U{0008}"[i] in "0123456789";
}

// REPEAT 10 - TIME: 8.217015 s

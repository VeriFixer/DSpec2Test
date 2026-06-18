// Clover_all_digits.dfy

method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
  result := true;
  for i := 0 to |""|
    invariant result <==> forall ii :: 0 <= ii < i ==> s[ii] in "0123456789"
  {
    if !(s[i] in "0123456789") {
      return false;
    }
  }
}


  method {:testEntry} allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
{
  result:=true ;
  for i := 0 to |s|
    invariant result <==> (forall ii :: 0 <= ii < i ==> s[ii] in "0123456789")
  {
    if ! (s[i] in "0123456789"){
      return false;
    }
  }
}

method {:test} Test0() {
var r0 := allDigits("aaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaa\0"| ==> "aaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 1 - TIME: 1.9990524 s

method {:test} Test1() {
var r0 := allDigits("aaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaa\0"| ==> "aaaaaa\0"[i] in "0123456789";
}

// REPEAT 2 - TIME: 2.7807159 s

method {:test} Test2() {
var r0 := allDigits("\U{0001}9");
expect r0 <==> forall i :: 0 <= i < |"\U{0001}9"| ==> "\U{0001}9"[i] in "0123456789";
}

// REPEAT 3 - TIME: 3.5239827 s

method {:test} Test3() {
var r0 := allDigits("9\0");
expect r0 <==> forall i :: 0 <= i < |"9\0"| ==> "9\0"[i] in "0123456789";
}

// REPEAT 4 - TIME: 4.2389437 s

method {:test} Test4() {
var r0 := allDigits("8aaaa\0");
expect r0 <==> forall i :: 0 <= i < |"8aaaa\0"| ==> "8aaaa\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 5.0561465 s

method {:test} Test5() {
var r0 := allDigits("0\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"0\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "0\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 6 - TIME: 5.7854257 s

method {:test} Test6() {
var r0 := allDigits("\0aaaaa\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaa\U{0002}\U{0004}"| ==> "\0aaaaa\U{0002}\U{0004}"[i] in "0123456789";
}

// REPEAT 7 - TIME: 6.4535415 s

method {:test} Test7() {
var r0 := allDigits("\U{0001}0aaaaaaaa");
expect r0 <==> forall i :: 0 <= i < |"\U{0001}0aaaaaaaa"| ==> "\U{0001}0aaaaaaaa"[i] in "0123456789";
}

// REPEAT 8 - TIME: 7.0427735 s

method {:test} Test8() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 9 - TIME: 7.7316038 s

method {:test} Test9() {
var r0 := allDigits("\09aa");
expect r0 <==> forall i :: 0 <= i < |"\09aa"| ==> "\09aa"[i] in "0123456789";
}

// REPEAT 10 - TIME: 8.2522326 s

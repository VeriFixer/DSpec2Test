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
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}

// REPEAT 1 - TIME: 1.8133906 s

method {:test} Test1() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}9");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}9"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}9"[i] in "0123456789";
}

// REPEAT 2 - TIME: 2.443466 s

method {:test} Test2() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}99");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}99"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}99"[i] in "0123456789";
}

// REPEAT 3 - TIME: 3.1010396 s

method {:test} Test3() {
var r0 := allDigits("0\U{0001}");
expect r0 <==> forall i :: 0 <= i < |"0\U{0001}"| ==> "0\U{0001}"[i] in "0123456789";
}

// REPEAT 4 - TIME: 3.920021 s

method {:test} Test4() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 5 - TIME: 4.7751507 s

method {:test} Test5() {
var r0 := allDigits("8\U{0002}aaaaaaaaaaaa9");
expect r0 <==> forall i :: 0 <= i < |"8\U{0002}aaaaaaaaaaaa9"| ==> "8\U{0002}aaaaaaaaaaaa9"[i] in "0123456789";
}

// REPEAT 6 - TIME: 5.6530931 s

method {:test} Test6() {
var r0 := allDigits("\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t");
expect r0 <==> forall i :: 0 <= i < |"\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t"| ==> "\U{0001}aa9aaaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t"[i] in "0123456789";
}

// REPEAT 7 - TIME: 6.5139662 s

method {:test} Test7() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 8 - TIME: 7.458909 s

method {:test} Test8() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 9 - TIME: 8.2929051 s

method {:test} Test9() {
var r0 := allDigits("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] in "0123456789";
}

// REPEAT 10 - TIME: 8.9369068 s

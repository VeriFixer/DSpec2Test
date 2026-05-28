  method {:testEntry}  allDigits(s: string) returns (result: bool)
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
var r0 := allDigits("a");
expect r0 <==> forall i :: 0 <= i < |"a"| ==> "a"[i] in "0123456789";
}
method {:test} Test1() {
var r0 := allDigits("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] in "0123456789";
}
method {:test} Test2() {
var r0 := allDigits("a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0");
expect r0 <==> forall i: int {:trigger "a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i]} :: 0 <= i < |"a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"| ==> "a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i] in "0123456789";
}
method {:test} Test3() {
var r0 := allDigits("a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}9");
expect r0 <==> forall i: int {:trigger "a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}9"[i]} :: 0 <= i < |"a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}9"| ==> "a9aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}9"[i] in "0123456789";
}
method {:test} Test4() {
var r0 := allDigits("99");
expect r0 <==> forall i: int {:trigger "99"[i]} :: 0 <= i < |"99"| ==> "99"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}aaaaaaaa9");
expect r0 <==> forall i: int {:trigger "\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}aaaaaaaa9"[i]} :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}aaaaaaaa9"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}aaaaaaaa9"[i] in "0123456789";
}
method {:test} Test6() {
var r0 := allDigits("10aaaa7aa");
expect r0 <==> forall i: int {:trigger "10aaaa7aa"[i]} :: 0 <= i < |"10aaaa7aa"| ==> "10aaaa7aa"[i] in "0123456789";
}
method {:test} Test7() {
var r0 := allDigits("\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a");
expect r0 <==> forall i: int {:trigger "\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a"[i]} :: 0 <= i < |"\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a"| ==> "\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9a"[i] in "0123456789";
}

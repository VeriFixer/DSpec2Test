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

method {:test} Test4() {
var r0 := allDigits("09");
expect r0 <==> forall i :: 0 <= i < |"09"| ==> "09"[i] in "0123456789";
}
method {:test} Test5() {
var r0 := allDigits("a\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a");
expect r0 <==> forall i :: 0 <= i < |"a\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| ==> "a\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"[i] in "0123456789";
}

// REPEAT 3 - TIME: 5.8926495 s

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

method {:test} Test12() {
var r0 := allDigits("18a0a");
expect r0 <==> forall i :: 0 <= i < |"18a0a"| ==> "18a0a"[i] in "0123456789";
}
method {:test} Test13() {
var r0 := allDigits("aaa\0a");
expect r0 <==> forall i :: 0 <= i < |"aaa\0a"| ==> "aaa\0a"[i] in "0123456789";
}

// REPEAT 7 - TIME: 62.7748539 s

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

method {:test} Test18() {
var r0 := allDigits("99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999");
expect r0 <==> forall i :: 0 <= i < |"99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999"| ==> "99a9aaaaaaaaaaaaa9aaaaa9aaaaaaaaaaaaaaa9a9999"[i] in "0123456789";
}
method {:test} Test19() {
var r0 := allDigits("\0aaaaa");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaa"| ==> "\0aaaaa"[i] in "0123456789";
}

// REPEAT 10 - TIME: 94.8059669 s

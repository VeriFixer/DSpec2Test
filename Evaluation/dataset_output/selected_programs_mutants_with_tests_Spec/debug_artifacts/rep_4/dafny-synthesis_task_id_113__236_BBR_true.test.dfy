// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if true {
    result := false;
  } else {
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result <==> forall k :: 0 <= k < i ==> IsDigit(s[k])
    {
      if !IsDigit(s[i]) {
        result := false;
        break;
      }
    }
  }
}

method {:test} Test7() {
var r0 := IsInteger("2a1");
expect r0 <==> |"2a1"| > 0 && forall i :: 0 <= i < |"2a1"| ==> IsDigit("2a1"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}");
expect r0 <==> |"\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}"| ==> IsDigit("\U{0002}a\U{0008}aaaa\0\U{0001}aaaaaaaa\U{0003}"[i]);
}

// REPEAT 4 - TIME: 10.0443884 s

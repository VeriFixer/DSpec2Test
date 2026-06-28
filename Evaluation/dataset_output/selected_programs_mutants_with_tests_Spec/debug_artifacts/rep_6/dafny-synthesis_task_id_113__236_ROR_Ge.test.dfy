// dafny-synthesis_task_id_113.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} IsInteger(s: string) returns (result: bool)
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  result := true;
  if |s| >= 0 {
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

method {:test} Test11() {
var r0 := IsInteger("3aaa4");
expect r0 <==> |"3aaa4"| > 0 && forall i :: 0 <= i < |"3aaa4"| ==> IsDigit("3aaa4"[i]);
}
method {:test} Test12() {
var r0 := IsInteger("\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}");
expect r0 <==> |"\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}"| > 0 && forall i :: 0 <= i < |"\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}"| ==> IsDigit("\U{0004}aa\U{0002}aa\0aa\U{0001}aa\"\U{0005}aaaaa\U{0003}a\U{0006}aaaaaaa\U{0007}"[i]);
}

// REPEAT 6 - TIME: 14.0993132 s

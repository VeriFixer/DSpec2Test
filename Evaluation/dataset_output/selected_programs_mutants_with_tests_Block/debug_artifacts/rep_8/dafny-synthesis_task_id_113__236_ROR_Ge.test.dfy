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

method {:test} Test14() {
var r0 := IsInteger("\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}");
expect r0 <==> |"\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}"| > 0 && forall i :: 0 <= i < |"\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}"| ==> IsDigit("\raaaaaaaaaaaaaa\U{0003}aa\U{0005}a\U{0007}aaa\taa\0a\U{000B}"[i]);
}
method {:test} Test15() {
var r0 := IsInteger("\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}");
expect r0 <==> |"\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}"| > 0 && forall i :: 0 <= i < |"\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}"| ==> IsDigit("\U{001B}a\U{0002}aa\U{0004}aaaa\U{000E}aaaaa\U{0006}aaaaaaa\0\U{000C}\na\U{0008}\U{0010}"[i]);
}

// REPEAT 8 - TIME: 11.7070815 s

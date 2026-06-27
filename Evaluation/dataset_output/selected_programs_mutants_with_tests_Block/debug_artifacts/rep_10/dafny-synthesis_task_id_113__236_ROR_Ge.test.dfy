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

method {:test} Test18() {
var r0 := IsInteger("\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}");
expect r0 <==> |"\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}"| > 0 && forall i :: 0 <= i < |"\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}"| ==> IsDigit("\r\0aaa\U{0001}aa\U{0002}\U{0003}a\U{0004}"[i]);
}
method {:test} Test19() {
var r0 := IsInteger("aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}");
expect r0 <==> |"aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}"| > 0 && forall i :: 0 <= i < |"aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}"| ==> IsDigit("aaa\U{0012}a\0a\U{0002}aaa\U{0006}\U{0004}\U{0008}"[i]);
}

// REPEAT 10 - TIME: 13.514132 s

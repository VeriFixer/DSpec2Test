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

method {:test} Test8() {
var r0 := IsInteger("\ta\0\U{0002}aa\U{0004}\U{0006}");
expect r0 <==> |"\ta\0\U{0002}aa\U{0004}\U{0006}"| > 0 && forall i :: 0 <= i < |"\ta\0\U{0002}aa\U{0004}\U{0006}"| ==> IsDigit("\ta\0\U{0002}aa\U{0004}\U{0006}"[i]);
}
method {:test} Test9() {
var r0 := IsInteger("\U{0019}a\0\U{0001}aaaaa\U{0002}");
expect r0 <==> |"\U{0019}a\0\U{0001}aaaaa\U{0002}"| > 0 && forall i :: 0 <= i < |"\U{0019}a\0\U{0001}aaaaa\U{0002}"| ==> IsDigit("\U{0019}a\0\U{0001}aaaaa\U{0002}"[i]);
}

// REPEAT 5 - TIME: 7.9753463 s

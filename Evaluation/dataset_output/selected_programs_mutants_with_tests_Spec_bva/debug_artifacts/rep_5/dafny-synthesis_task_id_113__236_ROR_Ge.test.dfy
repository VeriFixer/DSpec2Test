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

method {:test} Test26() {
var r0 := IsInteger("6a449");
expect r0 <==> |"6a449"| > 0 && forall i :: 0 <= i < |"6a449"| ==> IsDigit("6a449"[i]);
}
method {:test} Test27() {
var r0 := IsInteger("aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}");
expect r0 <==> |"aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}"| > 0 && forall i :: 0 <= i < |"aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}"| ==> IsDigit("aaaa\U{0018}aaaaaa\0aaa\U{0001}\U{0002}"[i]);
}

// REPEAT 5 - TIME: 20.066427 s

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

method {:test} Test7() {
var r0 := IsInteger("5aaaa4");
expect r0 <==> |"5aaaa4"| > 0 && forall i :: 0 <= i < |"5aaaa4"| ==> IsDigit("5aaaa4"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("aaaaaaaaa\U{0008}aa");
expect r0 <==> |"aaaaaaaaa\U{0008}aa"| > 0 && forall i :: 0 <= i < |"aaaaaaaaa\U{0008}aa"| ==> IsDigit("aaaaaaaaa\U{0008}aa"[i]);
}

// REPEAT 4 - TIME: 68.088361 s

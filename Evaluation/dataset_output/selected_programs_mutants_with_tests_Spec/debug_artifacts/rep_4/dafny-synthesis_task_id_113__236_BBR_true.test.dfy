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
var r0 := IsInteger("4aa24aaaaaaaa4");
expect r0 <==> |"4aa24aaaaaaaa4"| > 0 && forall i :: 0 <= i < |"4aa24aaaaaaaa4"| ==> IsDigit("4aa24aaaaaaaa4"[i]);
}
method {:test} Test8() {
var r0 := IsInteger("\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> |"\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"| > 0 && forall i :: 0 <= i < |"\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"| ==> IsDigit("\na\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i]);
}

// REPEAT 4 - TIME: 10.7133145 s

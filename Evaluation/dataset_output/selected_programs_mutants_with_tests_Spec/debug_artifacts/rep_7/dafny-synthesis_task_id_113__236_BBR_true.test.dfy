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

method {:test} Test13() {
var r0 := IsInteger("aaaaa4aaaaaaaa2a2441");
expect r0 <==> |"aaaaa4aaaaaaaa2a2441"| > 0 && forall i :: 0 <= i < |"aaaaa4aaaaaaaa2a2441"| ==> IsDigit("aaaaa4aaaaaaaa2a2441"[i]);
}
method {:test} Test14() {
var r0 := IsInteger("aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a");
expect r0 <==> |"aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a"| > 0 && forall i :: 0 <= i < |"aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a"| ==> IsDigit("aaaa\0\U{0001}aaaaaaaaaa\U{0002}\U{0003}\U{0008}a"[i]);
}

// REPEAT 7 - TIME: 15.2601795 s

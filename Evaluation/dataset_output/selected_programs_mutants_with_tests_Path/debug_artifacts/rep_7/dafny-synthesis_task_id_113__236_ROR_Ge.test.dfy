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

method {:test} Test13() {
var r0 := IsInteger("aa1a0aaaaaaaaaa");
expect r0 <==> |"aa1a0aaaaaaaaaa"| > 0 && forall i :: 0 <= i < |"aa1a0aaaaaaaaaa"| ==> IsDigit("aa1a0aaaaaaaaaa"[i]);
}
method {:test} Test14() {
var r0 := IsInteger("aaaaaaaaaaaaaa\t");
expect r0 <==> |"aaaaaaaaaaaaaa\t"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaaaaaa\t"| ==> IsDigit("aaaaaaaaaaaaaa\t"[i]);
}

// REPEAT 7 - TIME: 128.8954258 s

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

method {:test} Test0() {
var r0 := IsInteger("");
expect r0 <==> |""| > 0 && forall i :: 0 <= i < |""| ==> IsDigit(""[i]);
}
method {:test} Test1() {
var r0 := IsInteger("a");
expect r0 <==> |"a"| > 0 && forall i :: 0 <= i < |"a"| ==> IsDigit("a"[i]);
}
method {:test} Test2() {
var r0 := IsInteger("/");
expect r0 <==> |"/"| > 0 && forall i :: 0 <= i < |"/"| ==> IsDigit("/"[i]);
}

// REPEAT 1 - TIME: 4.5074394 s

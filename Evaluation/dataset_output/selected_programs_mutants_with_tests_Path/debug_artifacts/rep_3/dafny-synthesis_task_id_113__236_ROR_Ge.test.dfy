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

method {:test} Test5() {
var r0 := IsInteger("4a4a");
expect r0 <==> |"4a4a"| > 0 && forall i :: 0 <= i < |"4a4a"| ==> IsDigit("4a4a"[i]);
}
method {:test} Test6() {
var r0 := IsInteger("aa\U{0008}");
expect r0 <==> |"aa\U{0008}"| > 0 && forall i :: 0 <= i < |"aa\U{0008}"| ==> IsDigit("aa\U{0008}"[i]);
}

// REPEAT 3 - TIME: 50.2921467 s

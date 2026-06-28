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

method {:test} Test3() {
var r0 := IsInteger("a0");
expect r0 <==> |"a0"| > 0 && forall i :: 0 <= i < |"a0"| ==> IsDigit("a0"[i]);
}
method {:test} Test4() {
var r0 := IsInteger("\U{0008}\0");
expect r0 <==> |"\U{0008}\0"| > 0 && forall i :: 0 <= i < |"\U{0008}\0"| ==> IsDigit("\U{0008}\0"[i]);
}

// REPEAT 2 - TIME: 6.5337085 s

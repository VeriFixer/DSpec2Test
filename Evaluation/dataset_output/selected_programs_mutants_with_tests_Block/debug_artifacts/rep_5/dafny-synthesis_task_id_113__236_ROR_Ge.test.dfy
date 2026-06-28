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

method {:test} Test8() {
var r0 := IsInteger("\U{0008}a\0a");
expect r0 <==> |"\U{0008}a\0a"| > 0 && forall i :: 0 <= i < |"\U{0008}a\0a"| ==> IsDigit("\U{0008}a\0a"[i]);
}
method {:test} Test9() {
var r0 := IsInteger("\n\0");
expect r0 <==> |"\n\0"| > 0 && forall i :: 0 <= i < |"\n\0"| ==> IsDigit("\n\0"[i]);
}

// REPEAT 5 - TIME: 8.0855908 s

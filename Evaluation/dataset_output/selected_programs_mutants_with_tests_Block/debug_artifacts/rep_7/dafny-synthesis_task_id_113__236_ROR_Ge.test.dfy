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

method {:test} Test12() {
var r0 := IsInteger("\U{0007}a");
expect r0 <==> |"\U{0007}a"| > 0 && forall i :: 0 <= i < |"\U{0007}a"| ==> IsDigit("\U{0007}a"[i]);
}
method {:test} Test13() {
var r0 := IsInteger("%a\0aa");
expect r0 <==> |"%a\0aa"| > 0 && forall i :: 0 <= i < |"%a\0aa"| ==> IsDigit("%a\0aa"[i]);
}

// REPEAT 7 - TIME: 10.4528825 s

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

method {:test} Test22() {
var r0 := IsInteger("81a");
expect r0 <==> |"81a"| > 0 && forall i :: 0 <= i < |"81a"| ==> IsDigit("81a"[i]);
}
method {:test} Test23() {
var r0 := IsInteger("a\U{0001}\n\0");
expect r0 <==> |"a\U{0001}\n\0"| > 0 && forall i :: 0 <= i < |"a\U{0001}\n\0"| ==> IsDigit("a\U{0001}\n\0"[i]);
}

// REPEAT 3 - TIME: 21.6051437 s

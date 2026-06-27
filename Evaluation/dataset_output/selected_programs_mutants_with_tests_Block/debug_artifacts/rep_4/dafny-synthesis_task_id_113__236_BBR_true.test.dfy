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

method {:test} Test6() {
var r0 := IsInteger("\U{0007}a\0");
expect r0 <==> |"\U{0007}a\0"| > 0 && forall i :: 0 <= i < |"\U{0007}a\0"| ==> IsDigit("\U{0007}a\0"[i]);
}
method {:test} Test7() {
var r0 := IsInteger("\taa");
expect r0 <==> |"\taa"| > 0 && forall i :: 0 <= i < |"\taa"| ==> IsDigit("\taa"[i]);
}

// REPEAT 4 - TIME: 6.741605 s

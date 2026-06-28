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

method {:test} Test9() {
var r0 := IsInteger("21aaaaaaaaaaaaaaaaaa2");
expect r0 <==> |"21aaaaaaaaaaaaaaaaaa2"| > 0 && forall i :: 0 <= i < |"21aaaaaaaaaaaaaaaaaa2"| ==> IsDigit("21aaaaaaaaaaaaaaaaaa2"[i]);
}
method {:test} Test10() {
var r0 := IsInteger("\0a\U{0008}a");
expect r0 <==> |"\0a\U{0008}a"| > 0 && forall i :: 0 <= i < |"\0a\U{0008}a"| ==> IsDigit("\0a\U{0008}a"[i]);
}

// REPEAT 5 - TIME: 12.4035515 s

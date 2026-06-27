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

method {:test} Test22() {
var r0 := IsInteger("2aaaaa2aaaa4aa4");
expect r0 <==> |"2aaaaa2aaaa4aa4"| > 0 && forall i :: 0 <= i < |"2aaaaa2aaaa4aa4"| ==> IsDigit("2aaaaa2aaaa4aa4"[i]);
}
method {:test} Test23() {
var r0 := IsInteger("\0a\U{0008}a");
expect r0 <==> |"\0a\U{0008}a"| > 0 && forall i :: 0 <= i < |"\0a\U{0008}a"| ==> IsDigit("\0a\U{0008}a"[i]);
}

// REPEAT 3 - TIME: 17.2206176 s

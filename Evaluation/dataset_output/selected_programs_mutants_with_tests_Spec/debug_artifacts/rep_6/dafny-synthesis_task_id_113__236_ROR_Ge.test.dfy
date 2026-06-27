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

method {:test} Test11() {
var r0 := IsInteger("5a42aaaaa2aaaaaaaaa");
expect r0 <==> |"5a42aaaaa2aaaaaaaaa"| > 0 && forall i :: 0 <= i < |"5a42aaaaa2aaaaaaaaa"| ==> IsDigit("5a42aaaaa2aaaaaaaaa"[i]);
}
method {:test} Test12() {
var r0 := IsInteger("\U{0001}a\0\U{0018}\U{0002}");
expect r0 <==> |"\U{0001}a\0\U{0018}\U{0002}"| > 0 && forall i :: 0 <= i < |"\U{0001}a\0\U{0018}\U{0002}"| ==> IsDigit("\U{0001}a\0\U{0018}\U{0002}"[i]);
}

// REPEAT 6 - TIME: 13.5241505 s

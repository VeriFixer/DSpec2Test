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

method {:test} Test4() {
var r0 := IsInteger("\t\0");
expect r0 <==> |"\t\0"| > 0 && forall i :: 0 <= i < |"\t\0"| ==> IsDigit("\t\0"[i]);
}
method {:test} Test5() {
var r0 := IsInteger("\U{0008}\0aaaaaaaaaaaaaa\U{0001}");
expect r0 <==> |"\U{0008}\0aaaaaaaaaaaaaa\U{0001}"| > 0 && forall i :: 0 <= i < |"\U{0008}\0aaaaaaaaaaaaaa\U{0001}"| ==> IsDigit("\U{0008}\0aaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 5.2529837 s

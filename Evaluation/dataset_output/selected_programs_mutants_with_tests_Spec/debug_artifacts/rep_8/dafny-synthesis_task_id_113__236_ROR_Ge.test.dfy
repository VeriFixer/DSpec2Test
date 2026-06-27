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

method {:test} Test15() {
var r0 := IsInteger("aa4aa4aaaaaaaaaa97268aaaaaa7");
expect r0 <==> |"aa4aa4aaaaaaaaaa97268aaaaaa7"| > 0 && forall i :: 0 <= i < |"aa4aa4aaaaaaaaaa97268aaaaaa7"| ==> IsDigit("aa4aa4aaaaaaaaaa97268aaaaaa7"[i]);
}
method {:test} Test16() {
var r0 := IsInteger("\0a\U{0008}a\U{0002}\U{0001}");
expect r0 <==> |"\0a\U{0008}a\U{0002}\U{0001}"| > 0 && forall i :: 0 <= i < |"\0a\U{0008}a\U{0002}\U{0001}"| ==> IsDigit("\0a\U{0008}a\U{0002}\U{0001}"[i]);
}

// REPEAT 8 - TIME: 16.9296233 s

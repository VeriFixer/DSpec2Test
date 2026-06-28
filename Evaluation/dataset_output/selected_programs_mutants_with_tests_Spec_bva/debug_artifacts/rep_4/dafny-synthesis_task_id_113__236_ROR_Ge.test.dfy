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

method {:test} Test24() {
var r0 := IsInteger("aa0a1");
expect r0 <==> |"aa0a1"| > 0 && forall i :: 0 <= i < |"aa0a1"| ==> IsDigit("aa0a1"[i]);
}
method {:test} Test25() {
var r0 := IsInteger("\U{0001}\0a%\U{0002}");
expect r0 <==> |"\U{0001}\0a%\U{0002}"| > 0 && forall i :: 0 <= i < |"\U{0001}\0a%\U{0002}"| ==> IsDigit("\U{0001}\0a%\U{0002}"[i]);
}

// REPEAT 4 - TIME: 23.5171113 s

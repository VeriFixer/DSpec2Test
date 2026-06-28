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
var r0 := IsInteger("9aaaaaa1aaaaa422");
expect r0 <==> |"9aaaaaa1aaaaa422"| > 0 && forall i :: 0 <= i < |"9aaaaaa1aaaaa422"| ==> IsDigit("9aaaaaa1aaaaa422"[i]);
}
method {:test} Test16() {
var r0 := IsInteger("\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}");
expect r0 <==> |"\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}"| > 0 && forall i :: 0 <= i < |"\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}"| ==> IsDigit("\0aaaaaaa\"aaa\U{0001}\U{0003}\U{0002}"[i]);
}

// REPEAT 8 - TIME: 17.4371422 s

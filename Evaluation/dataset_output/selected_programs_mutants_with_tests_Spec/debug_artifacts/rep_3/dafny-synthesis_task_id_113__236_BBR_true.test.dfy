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

method {:test} Test5() {
var r0 := IsInteger("aaaaaaaaaa7a1");
expect r0 <==> |"aaaaaaaaaa7a1"| > 0 && forall i :: 0 <= i < |"aaaaaaaaaa7a1"| ==> IsDigit("aaaaaaaaaa7a1"[i]);
}
method {:test} Test6() {
var r0 := IsInteger("\U{0001}\0\U{0019}");
expect r0 <==> |"\U{0001}\0\U{0019}"| > 0 && forall i :: 0 <= i < |"\U{0001}\0\U{0019}"| ==> IsDigit("\U{0001}\0\U{0019}"[i]);
}

// REPEAT 3 - TIME: 8.6611614 s

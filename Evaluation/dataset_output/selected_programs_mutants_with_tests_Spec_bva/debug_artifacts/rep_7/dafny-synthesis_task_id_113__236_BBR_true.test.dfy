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

method {:test} Test30() {
var r0 := IsInteger("2aa4a98");
expect r0 <==> |"2aa4a98"| > 0 && forall i :: 0 <= i < |"2aa4a98"| ==> IsDigit("2aa4a98"[i]);
}
method {:test} Test31() {
var r0 := IsInteger("\U{0002}\0\U{0008}\U{0001}");
expect r0 <==> |"\U{0002}\0\U{0008}\U{0001}"| > 0 && forall i :: 0 <= i < |"\U{0002}\0\U{0008}\U{0001}"| ==> IsDigit("\U{0002}\0\U{0008}\U{0001}"[i]);
}

// REPEAT 7 - TIME: 29.288896 s

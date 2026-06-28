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

method {:test} Test26() {
var r0 := IsInteger("7a2aa");
expect r0 <==> |"7a2aa"| > 0 && forall i :: 0 <= i < |"7a2aa"| ==> IsDigit("7a2aa"[i]);
}
method {:test} Test27() {
var r0 := IsInteger("\U{0002}a\U{0008}\0\U{0001}\U{0003}");
expect r0 <==> |"\U{0002}a\U{0008}\0\U{0001}\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0002}a\U{0008}\0\U{0001}\U{0003}"| ==> IsDigit("\U{0002}a\U{0008}\0\U{0001}\U{0003}"[i]);
}

// REPEAT 5 - TIME: 25.4018902 s

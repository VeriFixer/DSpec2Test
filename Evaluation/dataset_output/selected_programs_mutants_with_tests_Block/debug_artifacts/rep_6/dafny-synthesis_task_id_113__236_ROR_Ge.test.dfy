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

method {:test} Test10() {
var r0 := IsInteger("\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}");
expect r0 <==> |"\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}"| > 0 && forall i :: 0 <= i < |"\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}"| ==> IsDigit("\U{0018}a\0\U{0003}aaaaaa\U{0005}a\U{0007}"[i]);
}
method {:test} Test11() {
var r0 := IsInteger("4\U{0019}a4");
expect r0 <==> |"4\U{0019}a4"| > 0 && forall i :: 0 <= i < |"4\U{0019}a4"| ==> IsDigit("4\U{0019}a4"[i]);
}

// REPEAT 6 - TIME: 9.5548049 s

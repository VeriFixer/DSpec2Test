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

method {:test} Test36() {
var r0 := IsInteger("7a4aaa6978");
expect r0 <==> |"7a4aaa6978"| > 0 && forall i :: 0 <= i < |"7a4aaa6978"| ==> IsDigit("7a4aaa6978"[i]);
}
method {:test} Test37() {
var r0 := IsInteger("aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}");
expect r0 <==> |"aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}"| > 0 && forall i :: 0 <= i < |"aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}"| ==> IsDigit("aaaa\U{0002}\U{0004}\U{0005}a\U{0008}\U{0007}\U{0006}\U{0001}\U{0003}\0\U{0008}"[i]);
}

// REPEAT 10 - TIME: 35.3232692 s

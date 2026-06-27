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

method {:test} Test20() {
var r0 := IsInteger("a01");
expect r0 <==> |"a01"| > 0 && forall i :: 0 <= i < |"a01"| ==> IsDigit("a01"[i]);
}
method {:test} Test21() {
var r0 := IsInteger("\U{0001}\0\U{0008}");
expect r0 <==> |"\U{0001}\0\U{0008}"| > 0 && forall i :: 0 <= i < |"\U{0001}\0\U{0008}"| ==> IsDigit("\U{0001}\0\U{0008}"[i]);
}

// REPEAT 2 - TIME: 15.4651045 s

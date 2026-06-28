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

method {:test} Test28() {
var r0 := IsInteger("9a22a4");
expect r0 <==> |"9a22a4"| > 0 && forall i :: 0 <= i < |"9a22a4"| ==> IsDigit("9a22a4"[i]);
}
method {:test} Test29() {
var r0 := IsInteger("\U{0001}aa\U{0008}\0");
expect r0 <==> |"\U{0001}aa\U{0008}\0"| > 0 && forall i :: 0 <= i < |"\U{0001}aa\U{0008}\0"| ==> IsDigit("\U{0001}aa\U{0008}\0"[i]);
}

// REPEAT 6 - TIME: 27.2280154 s

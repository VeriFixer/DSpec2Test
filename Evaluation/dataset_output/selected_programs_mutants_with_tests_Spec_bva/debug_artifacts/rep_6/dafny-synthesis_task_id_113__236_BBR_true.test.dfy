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

method {:test} Test28() {
var r0 := IsInteger("6424");
expect r0 <==> |"6424"| > 0 && forall i :: 0 <= i < |"6424"| ==> IsDigit("6424"[i]);
}
method {:test} Test29() {
var r0 := IsInteger("\U{0008}a");
expect r0 <==> |"\U{0008}a"| > 0 && forall i :: 0 <= i < |"\U{0008}a"| ==> IsDigit("\U{0008}a"[i]);
}

// REPEAT 6 - TIME: 21.369944 s

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

method {:test} Test19() {
var r0 := IsInteger("aaa76978aaaaaaaa28442a");
expect r0 <==> |"aaa76978aaaaaaaa28442a"| > 0 && forall i :: 0 <= i < |"aaa76978aaaaaaaa28442a"| ==> IsDigit("aaa76978aaaaaaaa28442a"[i]);
}
method {:test} Test20() {
var r0 := IsInteger("\U{0003}aa\U{0001}\U{0002}\0\U{0008}a");
expect r0 <==> |"\U{0003}aa\U{0001}\U{0002}\0\U{0008}a"| > 0 && forall i :: 0 <= i < |"\U{0003}aa\U{0001}\U{0002}\0\U{0008}a"| ==> IsDigit("\U{0003}aa\U{0001}\U{0002}\0\U{0008}a"[i]);
}

// REPEAT 10 - TIME: 19.9993202 s

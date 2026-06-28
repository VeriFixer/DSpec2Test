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

method {:test} Test34() {
var r0 := IsInteger("4798824982aaa1");
expect r0 <==> |"4798824982aaa1"| > 0 && forall i :: 0 <= i < |"4798824982aaa1"| ==> IsDigit("4798824982aaa1"[i]);
}
method {:test} Test35() {
var r0 := IsInteger("\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a");
expect r0 <==> |"\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a"| > 0 && forall i :: 0 <= i < |"\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a"| ==> IsDigit("\0a\"\U{0001}\U{0003}a\U{0002}\U{0004}a"[i]);
}

// REPEAT 9 - TIME: 33.5541379 s

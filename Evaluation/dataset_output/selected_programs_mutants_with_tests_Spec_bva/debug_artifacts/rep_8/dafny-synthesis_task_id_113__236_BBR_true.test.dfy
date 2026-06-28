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

method {:test} Test32() {
var r0 := IsInteger("2aa49a96");
expect r0 <==> |"2aa49a96"| > 0 && forall i :: 0 <= i < |"2aa49a96"| ==> IsDigit("2aa49a96"[i]);
}
method {:test} Test33() {
var r0 := IsInteger("\0aaa\U{0001}\U{0002}\U{0018}\U{0003}");
expect r0 <==> |"\0aaa\U{0001}\U{0002}\U{0018}\U{0003}"| > 0 && forall i :: 0 <= i < |"\0aaa\U{0001}\U{0002}\U{0018}\U{0003}"| ==> IsDigit("\0aaa\U{0001}\U{0002}\U{0018}\U{0003}"[i]);
}

// REPEAT 8 - TIME: 31.5122615 s

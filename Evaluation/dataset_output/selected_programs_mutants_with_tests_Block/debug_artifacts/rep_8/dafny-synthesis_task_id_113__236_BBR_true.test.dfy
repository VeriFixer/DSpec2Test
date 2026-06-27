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

method {:test} Test14() {
var r0 := IsInteger("\U{0005}aa\U{0001}\U{0003}");
expect r0 <==> |"\U{0005}aa\U{0001}\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0005}aa\U{0001}\U{0003}"| ==> IsDigit("\U{0005}aa\U{0001}\U{0003}"[i]);
}
method {:test} Test15() {
var r0 := IsInteger("\U{0018}aa\0\U{0002}\U{0004}");
expect r0 <==> |"\U{0018}aa\0\U{0002}\U{0004}"| > 0 && forall i :: 0 <= i < |"\U{0018}aa\0\U{0002}\U{0004}"| ==> IsDigit("\U{0018}aa\0\U{0002}\U{0004}"[i]);
}

// REPEAT 8 - TIME: 11.4977665 s

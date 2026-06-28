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

method {:test} Test10() {
var r0 := IsInteger("\U{0008}aa\U{0001}\U{0003}");
expect r0 <==> |"\U{0008}aa\U{0001}\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0008}aa\U{0001}\U{0003}"| ==> IsDigit("\U{0008}aa\U{0001}\U{0003}"[i]);
}
method {:test} Test11() {
var r0 := IsInteger("\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}");
expect r0 <==> |"\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}"| > 0 && forall i :: 0 <= i < |"\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}"| ==> IsDigit("\n\U{0001}a\U{0003}aaaa\U{0007}\U{0005}"[i]);
}

// REPEAT 6 - TIME: 9.6493108 s

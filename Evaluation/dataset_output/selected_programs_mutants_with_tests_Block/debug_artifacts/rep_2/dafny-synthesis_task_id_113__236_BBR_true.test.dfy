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

method {:test} Test2() {
var r0 := IsInteger("aaaaaa\U{0008}");
expect r0 <==> |"aaaaaa\U{0008}"| > 0 && forall i :: 0 <= i < |"aaaaaa\U{0008}"| ==> IsDigit("aaaaaa\U{0008}"[i]);
}
method {:test} Test3() {
var r0 := IsInteger("\U{0008}");
expect r0 <==> |"\U{0008}"| > 0 && forall i :: 0 <= i < |"\U{0008}"| ==> IsDigit("\U{0008}"[i]);
}

// REPEAT 2 - TIME: 4.0205401 s

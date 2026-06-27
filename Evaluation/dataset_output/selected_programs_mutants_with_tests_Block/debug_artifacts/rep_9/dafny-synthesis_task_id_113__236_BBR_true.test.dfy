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

method {:test} Test16() {
var r0 := IsInteger("\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}");
expect r0 <==> |"\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}"| > 0 && forall i :: 0 <= i < |"\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}"| ==> IsDigit("\U{0008}aaaa\U{0008}\0\n\U{0002}a\U{0006}\U{000E}a\U{000C}a\U{0004}a\U{0010}"[i]);
}
method {:test} Test17() {
var r0 := IsInteger("\naaa\0\U{0001}aaaa\U{0002}");
expect r0 <==> |"\naaa\0\U{0001}aaaa\U{0002}"| > 0 && forall i :: 0 <= i < |"\naaa\0\U{0001}aaaa\U{0002}"| ==> IsDigit("\naaa\0\U{0001}aaaa\U{0002}"[i]);
}

// REPEAT 9 - TIME: 12.524172 s

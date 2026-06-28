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

method {:test} Test12() {
var r0 := IsInteger("\U{0019}a\0\U{0003}");
expect r0 <==> |"\U{0019}a\0\U{0003}"| > 0 && forall i :: 0 <= i < |"\U{0019}a\0\U{0003}"| ==> IsDigit("\U{0019}a\0\U{0003}"[i]);
}
method {:test} Test13() {
var r0 := IsInteger("\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}");
expect r0 <==> |"\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}"| > 0 && forall i :: 0 <= i < |"\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}"| ==> IsDigit("\raaaaa\0aaaaaa\U{0007}aaa\U{0003}aaaaaa\U{0005}\ta\U{000B}"[i]);
}

// REPEAT 7 - TIME: 10.8163967 s

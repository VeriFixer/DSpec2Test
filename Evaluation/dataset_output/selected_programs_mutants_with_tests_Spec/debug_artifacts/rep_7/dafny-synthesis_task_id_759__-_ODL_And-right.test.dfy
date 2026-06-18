// dafny-synthesis_task_id_759.dfy

method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  ensures result ==> exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  ensures !result ==> !exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
  {
    if s[i] == '.' {
      result := true;
      break;
    }
  }
}

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\0");
expect r0 ==> exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r");
expect r0 ==> exists i :: 0 <= i < |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| && "\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"[i] == '.' && |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| && "\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"[i] == '.' && |"\U{000F}aa\U{0001}a\U{0005}aaaa\U{0007}aaa\ta\U{0003}a.\U{000B}\r"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 11.2183231 s

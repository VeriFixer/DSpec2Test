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

method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| && "\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"[i] == '.' && |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| && "\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"[i] == '.' && |"\U{0004}aaaa\U{0002}aaaaaaa\U{0008}\n\U{000C}aa\U{000E}aa\U{0006}aaaaaaa\0"| - i - 1 == 2;
}
method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| && "\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"[i] == '.' && |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| && "\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"[i] == '.' && |"\U{0003}a\U{0001}aaaaaaa\U{0005}aa\U{0007}\t.\U{000B}\r"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 16.9135188 s

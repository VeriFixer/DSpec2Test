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

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaa\U{0007}aa.\U{0005}\U{0001}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| && "\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '.' && |"\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 13.349977 s

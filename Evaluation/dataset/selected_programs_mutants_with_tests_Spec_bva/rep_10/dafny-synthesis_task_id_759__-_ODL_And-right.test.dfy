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

method {:test} Test30() {
var r0 := IsDecimalWithTwoPrecision("aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| && "aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"[i] == '.' && |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| && "aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"[i] == '.' && |"aaa\U{0008}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}\n\U{0006}"| - i - 1 == 2;
}
method {:test} Test31() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| && "aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"[i] == '.' && |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| && "aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"[i] == '.' && |"aa\U{0007}aa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0003}\U{0005}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 20.5766053 s

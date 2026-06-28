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

method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| && "\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"[i] == '.' && |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| && "\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"[i] == '.' && |"\U{0006}aaa\0aaaaaaaaa\U{0002}aaaa\U{0004}"| - i - 1 == 2;
}
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}\U{0005}.\U{0001}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}\U{0005}.\U{0001}a"| && "\U{0003}\U{0005}.\U{0001}a"[i] == '.' && |"\U{0003}\U{0005}.\U{0001}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}\U{0005}.\U{0001}a"| && "\U{0003}\U{0005}.\U{0001}a"[i] == '.' && |"\U{0003}\U{0005}.\U{0001}a"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 114.2840015 s

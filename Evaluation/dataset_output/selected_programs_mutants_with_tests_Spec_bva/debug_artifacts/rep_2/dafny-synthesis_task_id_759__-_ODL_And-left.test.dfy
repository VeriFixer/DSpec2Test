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
    if |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaa\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaa\U{0002}\0"| && "aaaaaaaaaaa\U{0002}\0"[i] == '.' && |"aaaaaaaaaaa\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaa\U{0002}\0"| && "aaaaaaaaaaa\U{0002}\0"[i] == '.' && |"aaaaaaaaaaa\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| && "\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"[i] == '.' && |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| && "\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"[i] == '.' && |"\U{0003}\U{0001}aaaaaaaaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0007}a"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 10.0310738 s

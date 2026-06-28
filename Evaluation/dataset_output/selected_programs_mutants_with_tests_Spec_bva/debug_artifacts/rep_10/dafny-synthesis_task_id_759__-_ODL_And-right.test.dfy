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
var r0 := IsDecimalWithTwoPrecision("\U{0006}a\0\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}a\0\U{0002}\U{0004}"| && "\U{0006}a\0\U{0002}\U{0004}"[i] == '.' && |"\U{0006}a\0\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}a\0\U{0002}\U{0004}"| && "\U{0006}a\0\U{0002}\U{0004}"[i] == '.' && |"\U{0006}a\0\U{0002}\U{0004}"| - i - 1 == 2;
}
method {:test} Test31() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| && "aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"[i] == '.' && |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| && "aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"[i] == '.' && |"aaaaa\taaa\U{0007}a\U{0001}a\ra\U{0005}\U{000B}a\U{0003}\U{000F}.\U{0011}a"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 27.7531612 s

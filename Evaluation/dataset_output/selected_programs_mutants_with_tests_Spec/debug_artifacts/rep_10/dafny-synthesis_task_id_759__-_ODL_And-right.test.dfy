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

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0\U{0004}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0\U{0004}a"| && "\U{0002}\0\U{0004}a"[i] == '.' && |"\U{0002}\0\U{0004}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0\U{0004}a"| && "\U{0002}\0\U{0004}a"[i] == '.' && |"\U{0002}\0\U{0004}a"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| && "aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"[i] == '.' && |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| && "aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"[i] == '.' && |"aa\U{0003}aaaaa\U{0005}\U{0001}\U{0007}aaa\U{000B}aaa\ra\U{000F}\t.a\U{0011}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 15.2846417 s

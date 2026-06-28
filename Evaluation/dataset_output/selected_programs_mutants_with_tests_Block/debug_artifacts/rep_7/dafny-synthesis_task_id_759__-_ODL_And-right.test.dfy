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
var r0 := IsDecimalWithTwoPrecision("\U{0004}aa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aa.\U{0002}\0"| && "\U{0004}aa.\U{0002}\0"[i] == '.' && |"\U{0004}aa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aa.\U{0002}\0"| && "\U{0004}aa.\U{0002}\0"[i] == '.' && |"\U{0004}aa.\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\U{0004}\0a\U{0006}aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\U{0004}\0a\U{0006}aa"| && "\U{0002}\U{0004}\0a\U{0006}aa"[i] == '.' && |"\U{0002}\U{0004}\0a\U{0006}aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\U{0004}\0a\U{0006}aa"| && "\U{0002}\U{0004}\0a\U{0006}aa"[i] == '.' && |"\U{0002}\U{0004}\0a\U{0006}aa"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 11.292394 s

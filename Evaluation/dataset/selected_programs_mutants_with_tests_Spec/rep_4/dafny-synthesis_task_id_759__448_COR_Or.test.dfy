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
    if s[i] == '.' || |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0"| && "\U{0002}\0"[i] == '.' && |"\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision(".\U{0001}\U{0003}");
expect r0 ==> exists i :: 0 <= i < |".\U{0001}\U{0003}"| && ".\U{0001}\U{0003}"[i] == '.' && |".\U{0001}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\U{0001}\U{0003}"| && ".\U{0001}\U{0003}"[i] == '.' && |".\U{0001}\U{0003}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 8.131228 s

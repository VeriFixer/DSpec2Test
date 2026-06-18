// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test3() {
var r0 := ContainsZ("a\0aaaaaaa\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"a\0aaaaaaa\U{0002}"| && ("a\0aaaaaaa\U{0002}"[i] == 'z' || "a\0aaaaaaa\U{0002}"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("\U{0003}aaaaaaaaaaaaaaaaaaa\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaaaaaaaa\U{0001}Z"| && ("\U{0003}aaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'z' || "\U{0003}aaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("Z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Z\U{0001}"| && ("Z\U{0001}"[i] == 'z' || "Z\U{0001}"[i] == 'Z');
}

// REPEAT 2 - TIME: 68.1405933 s

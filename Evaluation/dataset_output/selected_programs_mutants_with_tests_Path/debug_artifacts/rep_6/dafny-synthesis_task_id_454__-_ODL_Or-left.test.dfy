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

method {:test} Test15() {
var r0 := ContainsZ("\U{0004}\0aaaaa\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0aaaaa\U{0002}"| && ("\U{0004}\0aaaaa\U{0002}"[i] == 'z' || "\U{0004}\0aaaaa\U{0002}"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z");
expect r0 <==> exists i :: 0 <= i < |"aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z"| && ("aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z"[i] == 'z' || "aaa\0aaa\U{0002}aaaaaaaaa\U{0004}Z"[i] == 'Z');
}

// REPEAT 6 - TIME: 289.193226 s

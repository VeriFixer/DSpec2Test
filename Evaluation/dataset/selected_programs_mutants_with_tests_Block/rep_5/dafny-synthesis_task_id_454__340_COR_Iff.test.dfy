// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' <==> s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test8() {
var r0 := ContainsZ("\0Z");
expect r0 <==> exists i :: 0 <= i < |"\0Z"| && ("\0Z"[i] == 'z' || "\0Z"[i] == 'Z');
}
method {:test} Test9() {
var r0 := ContainsZ("zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa");
expect r0 <==> exists i :: 0 <= i < |"zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa"| && ("zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa"[i] == 'z' || "zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa"[i] == 'Z');
}

// REPEAT 5 - TIME: 8.4354947 s

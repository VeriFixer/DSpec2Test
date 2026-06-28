// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' <== s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test6() {
var r0 := ContainsZ("za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}"| && ("za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}"[i] == 'z' || "za\U{0002}aaa\0aaaaaaa\U{0006}aaaaaa\U{0004}\U{0008}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0002}aa\0aaaa\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aa\0aaaa\U{0004}\U{0006}"| && ("\U{0002}aa\0aaaa\U{0004}\U{0006}"[i] == 'z' || "\U{0002}aa\0aaaa\U{0004}\U{0006}"[i] == 'Z');
}

// REPEAT 4 - TIME: 6.8438237 s

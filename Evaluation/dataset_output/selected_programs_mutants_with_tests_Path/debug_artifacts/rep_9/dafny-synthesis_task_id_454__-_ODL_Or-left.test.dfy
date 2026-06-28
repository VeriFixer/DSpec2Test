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

method {:test} Test24() {
var r0 := ContainsZ("\U{0004}\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && ("\U{0004}\0\U{0002}"[i] == 'z' || "\U{0004}\0\U{0002}"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("aaZaaaaaaaaaaaaaa\0aaa");
expect r0 <==> exists i :: 0 <= i < |"aaZaaaaaaaaaaaaaa\0aaa"| && ("aaZaaaaaaaaaaaaaa\0aaa"[i] == 'z' || "aaZaaaaaaaaaaaaaa\0aaa"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("aZaaa");
expect r0 <==> exists i :: 0 <= i < |"aZaaa"| && ("aZaaa"[i] == 'z' || "aZaaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 632.0740673 s

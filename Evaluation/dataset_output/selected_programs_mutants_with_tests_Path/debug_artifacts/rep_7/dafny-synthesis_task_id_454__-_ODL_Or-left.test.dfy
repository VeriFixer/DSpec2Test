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

method {:test} Test18() {
var r0 := ContainsZ("\U{0008}\0aaa\U{0002}\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}\0aaa\U{0002}\U{0004}\U{0006}"| && ("\U{0008}\0aaa\U{0002}\U{0004}\U{0006}"[i] == 'z' || "\U{0008}\0aaa\U{0002}\U{0004}\U{0006}"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("aaaaaaaaaaaZaaaaaaaaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaZaaaaaaaaaaaaaaa"| && ("aaaaaaaaaaaZaaaaaaaaaaaaaaa"[i] == 'z' || "aaaaaaaaaaaZaaaaaaaaaaaaaaa"[i] == 'Z');
}

// REPEAT 7 - TIME: 469.5552503 s

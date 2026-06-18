// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] != 'z' || s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test6() {
var r0 := ContainsZ("za\0\U{0002}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"za\0\U{0002}\U{0004}"| && ("za\0\U{0002}\U{0004}"[i] == 'z' || "za\0\U{0002}\U{0004}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\0a\U{0002}\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\0a\U{0002}\U{0004}\U{0006}"| && ("\0a\U{0002}\U{0004}\U{0006}"[i] == 'z' || "\0a\U{0002}\U{0004}\U{0006}"[i] == 'Z');
}

// REPEAT 4 - TIME: 7.799926 s

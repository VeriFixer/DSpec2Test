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
var r0 := ContainsZ("\n\U{0008}\0a\U{0006}\U{0002}\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\n\U{0008}\0a\U{0006}\U{0002}\U{0004}"| && ("\n\U{0008}\0a\U{0006}\U{0002}\U{0004}"[i] == 'z' || "\n\U{0008}\0a\U{0006}\U{0002}\U{0004}"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}

// REPEAT 6 - TIME: 377.22965 s

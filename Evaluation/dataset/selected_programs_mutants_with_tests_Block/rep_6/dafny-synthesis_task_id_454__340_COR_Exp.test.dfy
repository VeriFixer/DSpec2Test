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

method {:test} Test10() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\0\U{0002}z");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}z"| && ("\0\U{0002}z"[i] == 'z' || "\0\U{0002}z"[i] == 'Z');
}

// REPEAT 6 - TIME: 9.665623 s

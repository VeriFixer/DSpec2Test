// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if true {
      result := true;
      break;
    }
  }
}

method {:test} Test4() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("\U{0002}a\0z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}a\0z"| && ("\U{0002}a\0z"[i] == 'z' || "\U{0002}a\0z"[i] == 'Z');
}

// REPEAT 3 - TIME: 6.5918238 s

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
var r0 := ContainsZ("Z\0");
expect r0 <==> exists i :: 0 <= i < |"Z\0"| && ("Z\0"[i] == 'z' || "Z\0"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("a\0z");
expect r0 <==> exists i :: 0 <= i < |"a\0z"| && ("a\0z"[i] == 'z' || "a\0z"[i] == 'Z');
}

// REPEAT 3 - TIME: 5.4000117 s

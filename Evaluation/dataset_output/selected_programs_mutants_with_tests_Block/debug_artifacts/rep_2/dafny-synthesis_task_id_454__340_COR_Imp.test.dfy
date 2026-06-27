// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'z' ==> s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test2() {
var r0 := ContainsZ("\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}Z"| && ("\U{0001}Z"[i] == 'z' || "\U{0001}Z"[i] == 'Z');
}
method {:test} Test3() {
var r0 := ContainsZ("a\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"a\U{0001}z"| && ("a\U{0001}z"[i] == 'z' || "a\U{0001}z"[i] == 'Z');
}

// REPEAT 2 - TIME: 4.5465304 s
